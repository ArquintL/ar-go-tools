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
	"runtime"
	"strings"
	"time"

	"github.com/awslabs/ar-go-tools/analysis"
	"github.com/awslabs/ar-go-tools/analysis/config"
	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/analysis/escape"
	"github.com/awslabs/ar-go-tools/analysis/lang"
	"github.com/awslabs/ar-go-tools/internal/analysisutil"
	"golang.org/x/tools/go/ssa"
)

type AnalysisResult struct {
	// TaintFlows contains all the data flows from the sources to the sinks detected during the analysis
	TaintFlows *Flows

	// State is the state at the end of the analysis, if you need to chain another analysis
	State *dataflow.AnalyzerState

	// Graph is the cross function dataflow graph built by the dataflow analysis. It contains the linked summaries of
	// each function appearing in the program and analyzed.
	Graph dataflow.InterProceduralFlowGraph

	// Errors contains a list of errors produced by the analysis. Errors may have been added at different steps of the
	// analysis.
	Errors []error
}

// Analyze runs the taint analysis on the program prog with the user-provided configuration config.
// If the analysis run successfully, a FlowInformation is returned, containing all the information collected.
// FlowInformation.SinkSources will map all the sinks encountered to the set of sources that reach them.
//
// - cfg is the configuration that determines which functions are sources, sinks and sanitizers.
//
// - prog is the built ssa representation of the program. The program must contain a main package and include all its
// dependencies, otherwise the pointer analysis will fail.
func Analyze(cfg *config.Config, prog *ssa.Program) (AnalysisResult, error) {
	// Number of working routines to use in parallel. TODO: make this an option?
	numRoutines := runtime.NumCPU() - 1
	if numRoutines <= 0 {
		numRoutines = 1
	}

	// ** First step **
	// - Running the pointer analysis over the whole program. We will query values only in
	// the user defined functions since we plan to analyze only user-defined functions. Any function from the runtime
	// or from the standard library that is called in the program should be summarized in the summaries package.
	// - Running the type analysis to map functions to their type

	state, err := dataflow.NewInitializedAnalyzerState(config.NewLogGroup(cfg), cfg, prog)
	if err != nil {
		return AnalysisResult{}, err
	}

	// Add interface implementations as sinks
	populateConfigInterfaces(state)

	// Optional step: running the escape analysis
	if cfg.UseEscapeAnalysis {
		state.Logger.Infof("Starting escape bottom-up analysis ...")
		start := time.Now()

		err := escape.InitializeEscapeAnalysisState(state)
		state.Logger.Infof("Escape bottom-up pass done (%.2f s).", time.Since(start).Seconds())

		if err != nil {
			return AnalysisResult{}, err
		}
	}

	// ** Second step **
	// The intra-procedural analysis is run on every function `f` such that `ignoreInFirstPass(f)` is
	// false. A dummy summary is inserted for every function that is not analyzed. If that dummy summary is needed
	// later in the inter-procedural analysis, then we [TODO: what do we do?].
	// The goal of this step is to build function summaries: a graph that represents how data flows through the
	// function being analyzed.

	// Only build summaries for non-stdlib functions here
	analysis.RunIntraProceduralPass(state, numRoutines,
		analysis.IntraAnalysisParams{
			ShouldBuildSummary: dataflow.ShouldBuildSummary,
			// For the intra-procedural pass, all source nodes of all problems are marked
			IsEntrypoint: IsSomeSourceNode,
		})

	// ** Third step **
	// the inter-procedural analysis is run over the entire program, which has been summarized in the
	// previous step by building function summaries. This analysis consists in checking whether there exists a sink
	// that is reachable from a source, for every taint tracking problem defined by the config.

	taintFlows := NewFlows()

	for _, taintSpec := range cfg.TaintTrackingProblems {
		visitor := NewVisitor(&taintSpec)
		analysis.RunInterProcedural(state, visitor, analysis.InterProceduralParams{
			// The entry points are specific to each taint tracking problem (unlike in the intra-procedural pass)
			IsEntrypoint: func(node ssa.Node) bool { return IsSourceNode(&taintSpec, node) },
		})

		taintFlows.Merge(visitor.taints)
	}

	// ** Fourth step **
	// Additional analyses are run after the taint analysis has completed. Those analyses check the soundness of the
	// result after the fact, and some other analyses can be used to prune false alarms.

	if state.HasErrors() {
		err = fmt.Errorf("analysis returned errors, check AnalysisResult.State for more details")
	}
	return AnalysisResult{State: state, Graph: *state.FlowGraph, TaintFlows: taintFlows}, err
}

// populateConfigInterfaces adds all the interface implementations for sinks to s.Config.TaintTrackingProblems.
func populateConfigInterfaces(s *dataflow.AnalyzerState) {
	newTaintSpecs := make([]config.TaintSpec, 0, len(s.Config.TaintTrackingProblems))
	for _, taintSpec := range s.Config.TaintTrackingProblems {
		for _, ci := range taintSpec.Sinks {
			if ci.Interface != "" {
				interfaceToImpls, ok := findImpls(s, ci)
				if !ok {
					continue
				}

				for interfaceMethodName, impls := range interfaceToImpls {
					split := strings.Split(interfaceMethodName, ".")
					if len(split) >= 3 {
						// e.g. github.com/repo/package.ReceiverType.Method
						//      ^^^^^^^^^^^^^^^^^^^^^^^ ^^^^^^^^^^^^ ^^^^^^
						//      package                 receiver     method
						iid := config.NewCodeIdentifier(config.CodeIdentifier{
							Package:  strings.Join(split[0:len(split)-2], "."),
							Receiver: split[len(split)-2],
							Method:   split[len(split)-1],
						})
						s.Logger.Infof("Interface: %+v\n", iid)
						// add the interface method
						taintSpec.Sinks = append(taintSpec.Sinks, iid)
					}

					for impl := range impls {
						// method receiver is the first parameter
						receiver := impl.Params[0]
						recvStr := analysisutil.ReceiverStr(receiver.Type())
						fid := config.NewCodeIdentifier(config.CodeIdentifier{
							Package:  lang.PackageNameFromFunction(impl),
							Receiver: recvStr,
							Method:   impl.Name(),
						})
						taintSpec.Sinks = append(taintSpec.Sinks, fid)
					}
				}
			}
		}

		// newTaintSpecs is needed because taintSpec is a copy
		newTaintSpecs = append(newTaintSpecs, taintSpec)
	}

	s.Config.TaintTrackingProblems = newTaintSpecs
}

// findImpls returns a map of the interface method name for ci's interface with all the interface implementations' methods.
// Requires that ci.Interface != "".
// TODO refactor to avoid string comparisons
func findImpls(s *dataflow.AnalyzerState, ci config.CodeIdentifier) (map[string]map[*ssa.Function]bool, bool) {
	res := make(map[string]map[*ssa.Function]bool)
	found := false
	for interfaceName, impls := range s.ImplementationsByType {
		if strings.Contains(interfaceName, ci.FullMethodName()) {
			res[interfaceName] = make(map[*ssa.Function]bool)
			for impl := range impls {
				res[interfaceName][impl] = true
				found = true
			}
		}
	}

	return res, found
}
