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
  [ annotationsC
  , characteristicsC
  , classC
  , classesC
  , dataPropertiesC
  , dataPropertyC
  , differentFromC
  , differentIndividualsC
  , disjointClassesC
  , disjointDataPropertiesC
  , disjointObjectPropertyC
  , disjointUnionOfC
  , disjointWithC
  , domainC
  , equivalentClassesC
  , equivalentDataPropertiesC
  , equivalentObjectPropertiesC
  , equivalentToC
  , factsC
  , importC
  , individualC
  , inverseOfC
  , inversesC
  , namespaceC
  , objectPropertiesC
  , objectPropertyC
  , ontologyC
  , paraphraseC
  , rangeC
  , sameAsC
  , sameIndividualC
  , subClassOfC
  , subPropertyChainC
  , subPropertyOfC
  , superPropertyChainC
  , superPropertyOfC
  , typesC
  , valuePartitionC
  ]

annotationsC :: String
annotationsC = "Annotations:"

characteristicsC :: String
characteristicsC = "Characteristics:"

classC :: String
classC = "Class:"

classesC :: String
classesC = "Classes:"

dataPropertiesC :: String
dataPropertiesC = "DataProperties:"

dataPropertyC :: String
dataPropertyC = "DataProperty:"

differentFromC :: String
differentFromC = "DifferentFrom:"

differentIndividualsC :: String
differentIndividualsC = "DifferentIndividuals:"

disjointClassesC :: String
disjointClassesC = "DisjointClasses:"

disjointDataPropertiesC :: String
disjointDataPropertiesC = "DisjointDataProperties:"

disjointObjectPropertyC :: String
disjointObjectPropertyC = "DisjointObjectProperty:"

disjointUnionOfC :: String
disjointUnionOfC = "DisjointUnionOf:"

disjointWithC :: String
disjointWithC = "DisjointWith:"

domainC :: String
domainC = "Domain:"

equivalentClassesC :: String
equivalentClassesC = "EquivalentClasses:"

equivalentDataPropertiesC :: String
equivalentDataPropertiesC = "EquivalentDataProperties:"

equivalentObjectPropertiesC :: String
equivalentObjectPropertiesC = "EquivalentObjectProperties:"

equivalentToC :: String
equivalentToC = "EquivalentTo:"

factsC :: String
factsC = "Facts:"

importC :: String
importC = "Import:"

individualC :: String
individualC = "Individual:"

inverseOfC :: String
inverseOfC = "InverseOf:"

inversesC :: String
inversesC = "Inverses:"

namespaceC :: String
namespaceC = "Namespace:"

objectPropertiesC :: String
objectPropertiesC = "ObjectProperties:"

objectPropertyC :: String
objectPropertyC = "ObjectProperty:"

ontologyC :: String
ontologyC = "Ontology:"

paraphraseC :: String
paraphraseC = "Paraphrase:"

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

superPropertyChainC :: String
superPropertyChainC = "SuperPropertyChain:"

superPropertyOfC :: String
superPropertyOfC = "SuperPropertyOf:"

typesC :: String
typesC = "Types:"

valuePartitionC :: String
valuePartitionC = "ValuePartition:"
