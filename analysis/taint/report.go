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
	"sort"

	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/analysis/lang"
	"github.com/awslabs/ar-go-tools/internal/colors"
	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/go/ssa"
)

type positionRange struct {
	Start token.Position
	End   token.Position
}

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

func getObjectPosRanges(c *dataflow.AnalyzerState, node dataflow.GraphNode) []positionRange {
	fileSet := c.Program.Fset
	start := node.Position(c)
	end := node.Position(c)
	switch n := node.(type) {
	case *dataflow.ParamNode:
		end.Column = start.Column + len(n.SsaNode().Name())
		return []positionRange{{start, end}}

	case *dataflow.CallNode:
		positions := getInstructionPosRanges(c, n.CallSite())
		// also add lhs if callNode is a non-go or defer call
		if callVal := n.CallSite().Value(); callVal != nil {
			if res := getInstructionValuePosRanges(n.CallSite(), callVal); res != nil {
				positions = append(positions, res...)
			}
		}
		return positions

	case *dataflow.CallNodeArg:
		var positions []positionRange
		if i, ok := n.Value().(ssa.Instruction); ok {
			positions = append(positions, getInstructionPosRanges(c, i)...)
		}

		if call := n.ParentNode().CallSite().Value(); call != nil {
			maybeStart, maybeEnd, err := getCallArgPosRange(call, n.Index())
			if err == nil {
				positions = append(positions, positionRange{maybeStart, maybeEnd})
			}
		}
		if len(positions) > 0 {
			return positions
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
			start = fileSet.Position(returnSlot.Pos())
			end = fileSet.Position(returnSlot.End())
		} else if fdec, ok := f.Syntax().(*ast.FuncLit); ok {
			returnSlot := fdec.Type.Results.List[n.Index()]
			start = fileSet.Position(returnSlot.Pos())
			end = fileSet.Position(returnSlot.End())
		}

	case *dataflow.ClosureNode:
		return getInstructionPosRanges(c, n.Instr())

	case *dataflow.BoundLabelNode:
		return getInstructionPosRanges(c, n.Instr())

	case *dataflow.SyntheticNode:

	case *dataflow.BoundVarNode:
		if i, ok := n.Value().(ssa.Instruction); ok {
			return getInstructionPosRanges(c, i)
		} else {
			c.Logger.Tracef("Couldn't figure out bound variable node %v\n", n)
		}

	case *dataflow.FreeVarNode:
		end.Column = start.Column + len(n.SsaNode().Name())

	case *dataflow.AccessGlobalNode:
		return getInstructionPosRanges(c, n.Instr())
	}
	if start.Column >= end.Column {
		end.Column += 4
	}
	return []positionRange{{start, end}}
}

// getInstructionPosRanges returns the position ranges of the instruction i, using either the value of the instructions
// or the information in the packages of the analyzer state, if available.
func getInstructionPosRanges(c *dataflow.AnalyzerState, i ssa.Instruction) []positionRange {
	if v, ok := i.(ssa.Value); ok {
		if res := getInstructionValuePosRanges(i, v); res != nil {
			return res
		}
	}
	start := lang.InstrPosToPosition(i, i.Pos())
	end := start
	end.Column += 4 // default value to capture positions around

	// attempt to get position information from the AST
	astFile := c.GetAstFile(i.Parent().Prog.Fset.File(i.Pos()))
	if astFile != nil {
		astNode, _ := astutil.PathEnclosingInterval(astFile, i.Pos(), i.Pos()+1)
		if len(astNode) > 0 {
			return []positionRange{{lang.InstrPosToPosition(i, astNode[0].Pos()),
				lang.InstrPosToPosition(i, astNode[0].End())}}
		}
	}
	return []positionRange{{start, end}}
}

// getInstructionValuePosRanges returns the position ranges of the value v, using the instruction's information
// to determine parent block and parent program.
func getInstructionValuePosRanges(i ssa.Instruction, v ssa.Value) []positionRange {
	for _, instr := range i.Block().Instrs {
		if dbg, ok := instr.(*ssa.DebugRef); ok {
			if dbg.X == v {
				return []positionRange{{lang.InstrPosToPosition(i, dbg.Expr.Pos()),
					lang.InstrPosToPosition(i, dbg.Expr.End())}}
			}
		}
	}
	return nil
}

// getCallArgPosRange returns the position range of the argument number argPos in the call c
func getCallArgPosRange(c *ssa.Call, argPos int) (token.Position, token.Position, error) {
	for _, instr := range c.Block().Instrs {
		if dbg, ok := instr.(*ssa.DebugRef); ok {
			if dbg.X == c {
				switch expr := dbg.Expr.(type) {
				case *ast.CallExpr:
					if len(expr.Args) > argPos {
						return c.Parent().Prog.Fset.Position(expr.Args[argPos].Pos()),
							c.Parent().Prog.Fset.Position(expr.Args[argPos].End()),
							nil
					} else {
						return token.Position{}, token.Position{}, fmt.Errorf("bad argument position")
					}
				}
			}
		}
	}
	return token.Position{}, token.Position{}, fmt.Errorf("did not find valid positions")
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
		positions := getObjectPosRanges(c, elt.Node)
		for _, pRange := range positions {
			s, err := genCoverageLine(c, pRange.Start, pRange.End)
			if err == nil {
				coverage[s] = true
			}
		}
	}
	// Add coverage data for all the instructions that are marked by the node. This represents better the positions
	// that have been visited by the analysis, since those instructions are the ones that were used to compute the
	// dataflow information. The data represented by the node has flowed to each of those instructions.
	for instr := range elt.Node.Marks() {
		pos = c.Program.Fset.Position(instr.Pos())
		if pos.IsValid() {
			if c.Config.MatchCoverageFilter(pos.Filename) {
				positions := getInstructionPosRanges(c, instr)
				for _, pRange := range positions {
					s, err := genCoverageLine(c, pRange.Start, pRange.End)
					if err == nil {
						coverage[s] = true
					}
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
