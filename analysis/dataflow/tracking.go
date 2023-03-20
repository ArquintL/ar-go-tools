package dataflow

import (
	"golang.org/x/tools/go/ssa"
)

// MarkType identifies different marks that can be propagated during the analysis.
// In the context of building function summaries, one can see the mark as a way to track where the data is flowing from.
// When running the taint analysis, the TaintedVal mark tracks tainted values.
// The design is open to the addition of other taint types.
type MarkType int

const (
	Parameter   MarkType = 1 << iota // A Parameter is a function parameter.
	FreeVar                          // A FreeVar is a free variable in a closure.
	TaintedVal                       // A TaintedVal is a value tainted by a taint source.
	CallSiteArg                      // A CallSiteArg is a call site argument.
	CallReturn                       // A CallReturn is a call site return.
	Closure                          // A Closure is a closure creation site
	BoundVar                         // A BoundVar is a variable bound by a closure
	Global                           // A Global is package global
	Synthetic                        // A Synthetic node type for any other node.
)

// Mark is a node with additional information about its type and region path (matching the paths in pointer analysis).
// This is used to mark dataflow between nodes.
type Mark struct {
	Node       ssa.Node
	RegionPath string
	Type       MarkType
	Qualifier  ssa.Value
}

// NewMark creates a source with a single type
func NewMark(node ssa.Node, typ MarkType, path string) Mark {
	return Mark{
		Node:       node,
		RegionPath: path,
		Type:       typ,
		Qualifier:  nil,
	}
}

// NewQualifierMark creates a source with a single type and a qualifier node
func NewQualifierMark(node ssa.Node, qualifier ssa.Value, typ MarkType, path string) Mark {
	return Mark{
		Node:       node,
		RegionPath: path,
		Type:       typ,
		Qualifier:  qualifier,
	}
}

// IsTainted returns true if the source is a taint source.
func (s *Mark) IsTainted() bool {
	return s.Type&TaintedVal != 0
}

// IsParameter returns true if the source is a function parameter.
func (s *Mark) IsParameter() bool {
	return s.Type&Parameter != 0
}

// IsFreeVar returns true if the source is a closure free variable.
func (s *Mark) IsFreeVar() bool {
	return s.Type&FreeVar != 0
}

// IsBoundVar returns true if the source is a closure free variable.
func (s *Mark) IsBoundVar() bool {
	return s.Type&BoundVar != 0
}

// IsClosure returns true if the source is a closure
func (s *Mark) IsClosure() bool {
	return s.Type&Closure != 0
}

// IsGlobal returns true if the source is a global
func (s *Mark) IsGlobal() bool {
	return s.Type&Global != 0
}

// IsCallSiteArg returns true if the source is a call site argument. If it returns true, then s.qualifier must be
// non-nil.
func (s *Mark) IsCallSiteArg() bool {
	return s.Type&CallSiteArg != 0
}

// IsCallReturn returns true if the source is a call return.
func (s *Mark) IsCallReturn() bool {
	return s.Type&CallReturn != 0
}

// IsSynthetic returns true if the source is synthetic.
func (s *Mark) IsSynthetic() bool {
	return s.Type&Synthetic != 0
}
