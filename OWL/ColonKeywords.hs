{- |
Module      :  $Header$
Description :  String constants for OWL colon keywords to be used for parsing
  and printing
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

String constants for keywords followed by a colon to be used for parsing and
printing

- all identifiers are mixed case
  the keyword is followed by a capital C to indicate the final colon
-}

module OWL.ColonKeywords where

colonKeywords :: [String]
colonKeywords =
  [ annotationPropertyC
  , annotationsC
  , characteristicsC
  , classC
  , dataPropertyC
  , datatypeC
  , differentFromC
  , differentIndividualsC
  , disjointUnionOfC
  , disjointWithC
  , domainC
  , equivalentToC
  , factsC
  , hasKeyC
  , importC
  , individualC
  , inverseOfC
  , objectPropertyC
  , ontologyC
  , prefixC
  , rangeC
  , sameAsC
  , sameIndividualC
  , subClassOfC
  , subPropertyChainC
  , subPropertyOfC
  , typesC ]

namespaceC :: String
namespaceC = "Namespace:"

annotationPropertyC :: String
annotationPropertyC = "AnnotationProperty:"

annotationsC :: String
annotationsC = "Annotations:"

characteristicsC :: String
characteristicsC = "Characteristics:"

classC :: String
classC = "Class:"

classesC :: String
classesC = "Classes:"

dataPropertyC :: String
dataPropertyC = "DataProperty:"

datatypeC :: String
datatypeC = "Datatype:"

differentFromC :: String
differentFromC = "DifferentFrom:"

differentIndividualsC :: String
differentIndividualsC = "DifferentIndividuals:"

disjointUnionOfC :: String
disjointUnionOfC = "DisjointUnionOf:"

disjointWithC :: String
disjointWithC = "DisjointWith:"

domainC :: String
domainC = "Domain:"

equivalentToC :: String
equivalentToC = "EquivalentTo:"

factsC :: String
factsC = "Facts:"

hasKeyC :: String
hasKeyC = "HasKey:"

importC :: String
importC = "Import:"

individualC :: String
individualC = "Individual:"

inverseOfC :: String
inverseOfC = "InverseOf:"

objectPropertyC :: String
objectPropertyC = "ObjectProperty:"

ontologyC :: String
ontologyC = "Ontology:"

prefixC :: String
prefixC = "Prefix:"

propertiesC :: String
propertiesC = "Properties:"

rangeC :: String
rangeC = "Range:"

sameAsC :: String
sameAsC = "SameAs:"

sameIndividualC :: String
sameIndividualC = "SameIndividual:"

subClassOfC :: String
subClassOfC = "SubClassOf:"

subPropertyChainC :: String
subPropertyChainC = "SubPropertyChain:"

subPropertyOfC :: String
subPropertyOfC = "SubPropertyOf:"

typesC :: String
typesC = "Types:"
