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
	"go/token"
	"io"
	"os"
	"sort"

	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/internal/colors"
)

func genCoverageLine(c *dataflow.AnalyzerState, pos token.Position) (string, error) {
	if !pos.IsValid() {
		return "", fmt.Errorf("position not valid")
	}
	if pos.Filename == "" {
		return "", fmt.Errorf("filename is empty")
	}
	
	s := fmt.Sprintf("%s:%d.%d,%d.100 1 1\n", pos.Filename, pos.Line, pos.Column, pos.Line)
	return s, nil
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
		s, err := genCoverageLine(c, pos)
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
				s, err := genCoverageLine(c, pos)
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
