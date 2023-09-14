// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package taint

import (
	"fmt"
	"go/ast"
	"go/token"
	"io"
	"os"
	"reflect"
	"sort"

	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/internal/colors"
	"golang.org/x/tools/go/ssa"
)

func genCoverageLine(c *dataflow.AnalyzerState, pos, end token.Position) (string, error) {
	if !pos.IsValid() {
		return "", fmt.Errorf("position not valid")
	}
	if pos.Filename == "" {
		return "", fmt.Errorf("filename is empty")
	}

	s := fmt.Sprintf("%s:%d.%d,%d.%d 1 1\n", pos.Filename, pos.Line, pos.Column, end.Line, end.Column)
	return s, nil
}

func getObjectPosRange(c *dataflow.AnalyzerState, node dataflow.GraphNode) (start, end token.Position) {
	fset := c.Program.Fset
	start = node.Position(c)
	end = node.Position(c)
	switch n := node.(type) {
	case *dataflow.ParamNode:
		end.Column = start.Column + len(n.SsaNode().Name())
	case *dataflow.CallNode:
		return getInstructionPosRange(n.CallSite())
	case *dataflow.CallNodeArg:
		if i, ok := n.Value().(ssa.Instruction); ok {
			return getInstructionPosRange(i)
		} else {
			// The argument is not an instruction, but something like a simple variable.
			// We want the range of the use of that value, not its definition, so we're going to
			// have to be more clever.
			fmt.Printf("Couldn't figure out call node arg %v\n", n)
		}
	case *dataflow.ReturnValNode:
		// Get the position of the return value declaration
		// if we have func f() (anInt int, error), then we should be able to find the ranges
		//                      ^^^^^
		//                                 ^^^^^

		f := n.Graph().Parent
		// For .Syntax to work, we need the
		if fdec, ok := f.Syntax().(*ast.FuncDecl); ok {
			returnSlot := fdec.Type.Results.List[n.Index()]
			start = fset.Position(returnSlot.Pos())
			end = fset.Position(returnSlot.End())
			// fmt.Printf("Found funcdecl %v %v\n", start, end)
		} else if fdec, ok := f.Syntax().(*ast.FuncLit); ok {
			returnSlot := fdec.Type.Results.List[n.Index()]
			start = fset.Position(returnSlot.Pos())
			end = fset.Position(returnSlot.End())
		}
	case *dataflow.ClosureNode:
	case *dataflow.BoundLabelNode:
	case *dataflow.SyntheticNode:
	case *dataflow.BoundVarNode:
	case *dataflow.FreeVarNode:
		end.Column = start.Column + len(n.SsaNode().Name())
	case *dataflow.AccessGlobalNode:
		return getInstructionPosRange(n.Instr())
	}
	if start.Column == end.Column {
		fmt.Printf("Warning, empty range for %v (type: %v)\n", node, reflect.TypeOf(node))
		end.Column += 1
	}
	return
}
func getInstructionPosRange(i ssa.Instruction) (start, end token.Position) {
	if v, ok := i.(ssa.Value); ok {
		for _, instr := range i.Block().Instrs {
			if dbg, ok := instr.(*ssa.DebugRef); ok {
				if dbg.X == v {
					start = i.Parent().Prog.Fset.Position(dbg.Expr.Pos())
					end = i.Parent().Prog.Fset.Position(dbg.Expr.End())
					return start, end
				}
			}
		}
	}
	start = i.Parent().Prog.Fset.Position(i.Pos())
	end = i.Parent().Prog.Fset.Position(i.Pos())
	end.Column += 1
	fmt.Printf("Warning, empty range for %v (type: %v)\n", i, reflect.TypeOf(i))
	return start, end
}

// addCoverage adds an entry to coverage by properly formatting the position of the visitorNode in the context of
// the analyzer state
func addCoverage(c *dataflow.AnalyzerState, elt *dataflow.VisitorNode, coverage map[string]bool) {
	if coverage == nil {
		return
	}
	// Add coverage data for the position of the node
	pos := elt.Node.Position(c)
	if c.Config.MatchCoverageFilter(pos.Filename) {
		a, b := getObjectPosRange(c, elt.Node)
		s, err := genCoverageLine(c, a, b)
		if err == nil {
			coverage[s] = true
		}
	}
	// Add coverage data for all the instructions that are marked by the node. This represents better the positions
	// that have been visited by the analysis, since those instructions are the ones that were used to compute the
	// dataflow information. The data represented by the node has flowed to each of those instructions.
	for instr := range elt.Node.Marks() {
		pos = c.Program.Fset.Position(instr.Pos())
		if pos.IsValid() {
			if c.Config.MatchCoverageFilter(pos.Filename) {
				a, b := getInstructionPosRange(instr)
				s, err := genCoverageLine(c, a, b)
				if err == nil {
					coverage[s] = true
				}
			}
		}
	}
}

// reportCoverage writes the coverage data contains in the coverage map to the coverageWriter
// The strings in the coverage map are sorted and then written to the coverage writer
func reportCoverage(coverage map[string]bool, coverageWriter io.StringWriter) {
	if coverageWriter != nil {
		var cov []string
		for covered := range coverage {
			cov = append(cov, covered)
		}
		sort.Slice(cov, func(i int, j int) bool { return cov[i] < cov[j] })

		for _, line := range cov {
			coverageWriter.WriteString(line)
		}
	}
}

// reportTaintFlow reports a taint flow by writing to a file if the configuration has the ReportPaths flag set,
// and writing in the logger
func reportTaintFlow(c *dataflow.AnalyzerState, source dataflow.NodeWithTrace, sink *dataflow.VisitorNode) {
	c.Logger.Infof(" 💀 Sink reached at %s\n", colors.Red(sink.Node.Position(c)))
	c.Logger.Infof(" Add new path from %s to %s <== \n",
		colors.Green(source.Node.String()), colors.Red(sink.Node.String()))
	sinkPos := sink.Node.Position(c)
	if callArg, isCallArgsink := sink.Node.(*dataflow.CallNodeArg); isCallArgsink {
		sinkPos = callArg.ParentNode().Position(c)
	}
	if c.Config.ReportPaths {
		tmp, err := os.CreateTemp(c.Config.ReportsDir, "flow-*.out")
		if err != nil {
			c.Logger.Errorf("Could not write report.")
		}
		defer tmp.Close()
		c.Logger.Infof("Report in %s\n", tmp.Name())

		tmp.WriteString(fmt.Sprintf("Source: %s\n", source.Node.String()))
		tmp.WriteString(fmt.Sprintf("At: %s\n", source.Node.Position(c)))
		tmp.WriteString(fmt.Sprintf("Sink: %s\n", sink.Node.String()))
		tmp.WriteString(fmt.Sprintf("At: %s\n", sinkPos))

		nodes := []*dataflow.VisitorNode{}
		cur := sink
		for cur != nil {
			nodes = append(nodes, cur)
			cur = cur.Prev
		}

		tmp.WriteString(fmt.Sprintf("Trace:\n"))
		for i := len(nodes) - 1; i >= 0; i-- {
			if nodes[i].Status.Kind != dataflow.DefaultTracing {
				continue
			}
			tmp.WriteString(fmt.Sprintf("%s\n", nodes[i].Node.Position(c).String()))
			c.Logger.Infof("%s - %s",
				colors.Purple("TRACE"),
				dataflow.NodeSummary(nodes[i].Node))
			c.Logger.Infof("%s - %s [%s] %s\n",
				"     ",
				dataflow.NodeKind(nodes[i].Node),
				dataflow.FuncNames(nodes[i].Trace),
				nodes[i].Node.Position(c).String())
		}
		c.Logger.Infof("-- SINK: %s\n", sinkPos.String())
	}
}
