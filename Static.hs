{- |
This folder contains the static analysis of heterogeneous
specifications (which is based on the static analysis
of basic specifications, as provided by the individual logics).

"Static.DevGraph" contains data structures for
heterogeneous development graphs,
which are the result of the static analysis.
Heterogeneous development graphs are based on the Grothendieck
logic implemented by the module "Logic.Grothendieck".

"Static.PrintDevGraph" provides pretty printing for development graphs.
"Static.DotGraph" draws a development graph using the
dot tool <http://www.graphviz.org/>.

"Static.AnalysisStructured" provides the static analysis of
heterogeneous structured specifications,
"Static.AnalysisArchitecture" that of architectural specifications,
and
"Static.AnalysisLibrary" that of libraries.
"Static.ArchDiagram" contains the amalgamability analysis for
architectural diagrams, needed for the extended static semantics
of architectural specifications.

-}

module Static where
