{- |

The "OWL_DL" folder contains the OWL-DL 1.0 (see
<http://www.w3.org/TR/owl-features/>) instance of "Logic.Logic".  All the
data for this instance is assembled in "OWL_DL.Logic_OWL_DL".

/Abstract Syntax/

The abstract syntax of OWL-DL basic specifications is provided in
"OWL_DL.AS" as a Haskell algebraic datatype.  It largely
follows the OWL Web Ontology Language Semantics and Abstract Syntax
W3C Recommendation 10 Feb 2004. Patel-Schneider, Hayes, Horrocks, eds.
 (see <http://www.w3.org/TR/owl-semantics/>).

/Parser/

The OWL-DL parser is contained in OWL_DL\/java and it is written in Java.
It reuses the Manchester OWL API as it is part of Pellet 1.1.0
<http://pellet.owldl.com/> for the parsing of an OWL-DL file together
with all its imports. The result is communicated to Hets via an unshared
ATerm file. Implementation of the ATerm conversion ("OWL_DL.ReadWrite")
is largely derived
from the Haskell datatypes in "OWL_DL.AS". The calling of the Java program
is achieved in "OWL_DL.OWLAnalysis", which in fact provides parsing
into a development graph.

/Printing/

 Pretty printing (based on "Common.Lib.Pretty")
of OWL-DL basic specifications is provided in
"OWL_DL.Print". It follows the syntax of Common Lisp and this tranlation:
 <http://www.ihmc.us/users/phayes/CL/SW2SCL.html>

A LaTeX output is not available, yet.

/Signatures and Sentences/

The data structures for OWL_DL signatures are contained in "OWL_DL.Sign".
  OWL-DL sentences are represented as abstract syntax trees of type
'OWL_DL.Sign.Sentence', which is the union of types 'OWL_DL.AS.Axiom' and
'OWL_DL.AS.Fact'.

/Static Analysis/

The main module for static analysis of OWL-DL basic specifications is
"OWL_DL.StaticAna". The outcome basically is a signature and a set of
sentences.
"OWL_DL.StructureAna" contains the structured analysis of OWL_DL.

/Miscellaneous/

"OWL_DL.Namespace" provides a transformation function for namespaces down
the abstract syntax defined in "OWL_DL.AS".

OWL_DL\/ToHaskellAS.hs provides a test program for calling the Java parser
and analysing its result.

Additional details maybe obtained from the LaTeX document owl-casl-doc_en.tex
in OWL_DL\/doc.

-}

module OWL_DL where
