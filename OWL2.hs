{- | 
Description :  Web Ontology Language OWL2
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt

The "OWL2" directory contains the OWL2 instance of "Logic.Logic".
The data for this instance is found in "OWL2.Logic_OWL2".

/Abstact Syntax/

The syntax for OWL2 is represented using Haskell datatypes. It is defined both in
OWL2.AS - which contains the entities and expressions (<http://www.w3.org/TR/owl2-syntax/>)
and in OWL2.MS - which contains the frames (<http://www.w3.org/TR/owl2-manchester-syntax/>).
As the official Manchester Syntax cannot express some of the valid OWL2 axioms,
the Haskell datatypes for frames were extended to also accomodate these.

/Parser/

The parsing of an OWL ontology happens in two main steps. First, the ontology is
converted to XML, using the Java parser found in "OWL2.java". Then, the XML is
parsed into the Haskell datatypes (see "OWL2.XML"). The top-level function which
combines the two steps is found in "OWL2.ParseOWLAsLibDefn".

The parser for the Het-CASL representation is found in "OWL2.Parse" and
"OWL2.ManchesterParser" which take as argument an ontology in our extended
Manchester Syntax and convert it into the Haskell datatypes.

/Pretty printing/

This is done in "OWL2.Print" (for the "AS.hs" datatypes) and in
"OWL2.ManchesterPrint" (fot the "MS.hs" datatypes). The output is written
in our extended Manchester Syntax.

A LaTeX output is not available, yet.

/Static Analysis/

The file "OWL2.StaticAnalysis" repairs the ontology after parsing and then
produces the final axioms and signature needed for hets analysis.

/Provers/

There are two of these for OWL2, namely Pellet and FACT++, written in Java.
The call for them happens in "OWL2.ProvePellet" and "OWL2.ProveFact". The input
for the provers is XML syntax, which comes from "OWL2.XMLConversion". The
conservativity check is implemented in "OWL2.Conservativity" and uses the Java-
written locality checker.

/Comorphisms/

There are three implemented comorphsims: from OWL2 to CASL and Common Logic
and from DMU to OWL2.

/Profiles and sublogics/

There are three OWL2 profiles: EL, QL and RL. In "OWL2.Profiles", an ontology
is taken as argument and analysed, in order to see in which of the profiles it
fits, while in "OWL2.Sublogics", the reasoning complexity of the ontology
is computed.

/Miscellaneous/

"OWL2.Function" provides a class for functions which go through all the Haskell
datatypes and which are structurally equivalent (except maybe on what they do
with the IRIs or entities). Currently, morphism mapping, prefix renaming
and IRI expansion are implemented there.

"OWL2.ColimSign" and "OWL2.Taxonomy" provide signature colimits and taxonomy
extraction, respectively.

-}

module OWL2 where
