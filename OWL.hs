{- |

The "OWL" folder contains the OWL 1.1 (see
<http://www.w3.org/Submission/2006/10/>) instance of "Logic.Logic".  All the
data for this instance is assembled in "OWL.Logic_OWL".

/Abstract Syntax/

The abstract syntax of OWL basic specifications is provided in
"OWL.AS" as a Haskell algebraic datatype.  It largely
follows the OWL Web Ontology Language Semantics and Abstract Syntax
W3C Member Submission 19 December 2006. Boris Motik, Peter F. Patel-Schneider, Ian Horrocks, eds.
 (see <http://www.w3.org/Submission/2006/SUBM-owl11-owl_specification-20061219/>).

/Parser/

The OWL parser is contained in OWL and it is written in Java.
It reuses the Manchester OWL API as it is part of Pellet 2.1.1
<http://owlapi.sourceforge.net/> for the parsing of an OWL file together
with all its imports. The result is communicated to Hets via an unshared
ATerm file. Implementation of the ATerm conversion ("OWL.ReadWrite")
is largely derived
from the Haskell datatypes in "OWL.AS". The calling of the Java program
is achieved in "OWL.OWLAnalysis", which in fact provides parsing
into a development graph.

/Printing/

 Pretty printing (based on "Common.Lib.Pretty")
of OWL basic specifications is provided in
"OWL.Print".

A LaTeX output is not available, yet.

/Signatures and Sentences/

The data structures for OWL signatures are contained in "OWL.Sign".
  OWL 1.1 sentences are represented as abstract syntax trees of type
'OWL.Sign.Sentence'.

/Static Analysis/

The main module for static analysis of OWL 1.1 basic specifications is
"OWL.StaticAnalysis". The outcome basically is a signature and a set of
sentences. "OWL.StructureAnalysis" contains the structured analysis of OWL 1.1.

/Miscellaneous/

"OWL.Namespace" provides a transformation function for namespaces down
the abstract syntax defined in "OWL.AS".

OWL\/OWLParser.hs provides a test program for calling the Java parser
and analysing its result.

Additional details maybe obtained from the LaTeX document owl-casl-doc_en.tex
in OWL\/doc.

-}

module OWL where
