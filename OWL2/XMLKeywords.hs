{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Kewyords used for XML.hs and XMLConversion.hs
-}

module OWL2.XMLKeywords where

ontologyIRIK :: String
ontologyIRIK = "ontologyIRI"

iriK :: String
iriK = "IRI"

abbreviatedIRIK :: String
abbreviatedIRIK = "abbreviatedIRI"

nodeIDK :: String
nodeIDK = "nodeID"

prefixK :: String
prefixK = "Prefix"

importK :: String
importK = "Import"

classK :: String
classK = "Class"

datatypeK :: String
datatypeK = "Datatype"

namedIndividualK :: String
namedIndividualK = "NamedIndividual"

objectPropertyK :: String
objectPropertyK = "ObjectProperty"

dataPropertyK :: String
dataPropertyK = "DataProperty"

annotationPropertyK :: String
annotationPropertyK = "AnnotationProperty"

anonymousIndividualK :: String
anonymousIndividualK = "AnonymousIndividual"

facetRestrictionK :: String
facetRestrictionK = "FacetRestriction"

literalK :: String
literalK = "Literal"

declarationK :: String
declarationK = "Declaration"

annotationK :: String
annotationK = "Annotation"

objectInverseOfK :: String
objectInverseOfK = "ObjectInverseOf"

datatypeRestrictionK :: String
datatypeRestrictionK = "DatatypeRestriction"

dataComplementOfK :: String
dataComplementOfK = "DataComplementOf"

dataOneOfK :: String
dataOneOfK = "DataOneOf"

dataIntersectionOfK :: String
dataIntersectionOfK = "DataIntersectionOf"

dataUnionOfK :: String
dataUnionOfK = "DataUnionOf"

objectIntersectionOfK :: String
objectIntersectionOfK = "ObjectIntersectionOf"

objectUnionOfK :: String
objectUnionOfK = "ObjectUnionOf"

objectComplementOfK :: String
objectComplementOfK = "ObjectComplementOf"

objectOneOfK :: String
objectOneOfK = "ObjectOneOf"

objectSomeValuesFromK :: String
objectSomeValuesFromK = "ObjectSomeValuesFrom"

objectAllValuesFromK :: String
objectAllValuesFromK = "ObjectAllValuesFrom"

objectHasValueK :: String
objectHasValueK = "ObjectHasValue"

objectHasSelfK :: String
objectHasSelfK = "ObjectHasSelf"

objectMinCardinalityK :: String
objectMinCardinalityK = "ObjectMinCardinality"

objectMaxCardinalityK :: String
objectMaxCardinalityK = "ObjectMaxCardinality"

objectExactCardinalityK :: String
objectExactCardinalityK = "ObjectExactCardinality"

dataSomeValuesFromK :: String
dataSomeValuesFromK = "DataSomeValuesFrom"

dataAllValuesFromK :: String
dataAllValuesFromK = "DataAllValuesFrom"

dataHasValueK :: String
dataHasValueK = "DataHasValue"

dataMinCardinalityK :: String
dataMinCardinalityK = "DataMinCardinality"

dataMaxCardinalityK :: String
dataMaxCardinalityK = "DataMaxCardinality"

dataExactCardinalityK :: String
dataExactCardinalityK = "DataExactCardinality"

subClassOfK :: String
subClassOfK = "SubClassOf"

equivalentClassesK :: String
equivalentClassesK = "EquivalentClasses"

disjointClassesK :: String
disjointClassesK = "DisjointClasses"

disjointUnionK :: String
disjointUnionK = "DisjointUnion"

datatypeDefinitionK :: String
datatypeDefinitionK = "DatatypeDefinition"

hasKeyK :: String
hasKeyK = "HasKey"

subObjectPropertyOfK :: String
subObjectPropertyOfK = "SubObjectPropertyOf"

objectPropertyChainK :: String
objectPropertyChainK = "ObjectPropertyChain"

equivalentObjectPropertiesK :: String
equivalentObjectPropertiesK = "EquivalentObjectProperties"

disjointObjectPropertiesK :: String
disjointObjectPropertiesK = "DisjointObjectProperties"

objectPropertyDomainK :: String
objectPropertyDomainK = "ObjectPropertyDomain"

objectPropertyRangeK :: String
objectPropertyRangeK = "ObjectPropertyRange"

inverseObjectPropertiesK :: String
inverseObjectPropertiesK = "InverseObjectProperties"

functionalObjectPropertyK :: String
functionalObjectPropertyK = "FunctionalObjectProperty"

inverseFunctionalObjectPropertyK :: String
inverseFunctionalObjectPropertyK = "InverseFunctionalObjectProperty"

reflexiveObjectPropertyK :: String
reflexiveObjectPropertyK = "ReflexiveObjectProperty"

irreflexiveObjectPropertyK :: String
irreflexiveObjectPropertyK = "IrreflexiveObjectProperty"

symmetricObjectPropertyK :: String
symmetricObjectPropertyK = "SymmetricObjectProperty"

asymmetricObjectPropertyK :: String
asymmetricObjectPropertyK = "AsymmetricObjectProperty"

antisymmetricObjectPropertyK :: String
antisymmetricObjectPropertyK = "AntisymmetricObjectProperty"

transitiveObjectPropertyK :: String
transitiveObjectPropertyK = "TransitiveObjectProperty"

subDataPropertyOfK :: String
subDataPropertyOfK = "SubDataPropertyOf"

equivalentDataPropertiesK :: String
equivalentDataPropertiesK = "EquivalentDataProperties"

disjointDataPropertiesK :: String
disjointDataPropertiesK = "DisjointDataProperties"

dataPropertyDomainK :: String
dataPropertyDomainK = "DataPropertyDomain"

dataPropertyRangeK :: String
dataPropertyRangeK = "DataPropertyRange"

functionalDataPropertyK :: String
functionalDataPropertyK = "FunctionalDataProperty"

dataPropertyAssertionK :: String
dataPropertyAssertionK = "DataPropertyAssertion"

negativeDataPropertyAssertionK :: String
negativeDataPropertyAssertionK = "NegativeDataPropertyAssertion"

objectPropertyAssertionK :: String
objectPropertyAssertionK = "ObjectPropertyAssertion"

negativeObjectPropertyAssertionK :: String
negativeObjectPropertyAssertionK = "NegativeObjectPropertyAssertion"

sameIndividualK :: String
sameIndividualK = "SameIndividual"

differentIndividualsK :: String
differentIndividualsK = "DifferentIndividuals"

classAssertionK :: String
classAssertionK = "ClassAssertion"

annotationAssertionK :: String
annotationAssertionK = "AnnotationAssertion"

subAnnotationPropertyOfK :: String
subAnnotationPropertyOfK = "SubAnnotationPropertyOf"

annotationPropertyDomainK :: String
annotationPropertyDomainK = "AnnotationPropertyDomain"

annotationPropertyRangeK :: String
annotationPropertyRangeK = "AnnotationPropertyRange"

entityList :: [String]
entityList = [classK, datatypeK, namedIndividualK,
    objectPropertyK, dataPropertyK, annotationPropertyK]

individualList :: [String]
individualList = [namedIndividualK, anonymousIndividualK]

objectPropList :: [String]
objectPropList = [objectPropertyK, objectInverseOfK]

dataPropList :: [String]
dataPropList = [dataPropertyK]

dataRangeList :: [String]
dataRangeList = [datatypeK, datatypeRestrictionK, dataComplementOfK,
      dataOneOfK, dataIntersectionOfK, dataUnionOfK]

classExpressionList :: [String]
classExpressionList = [classK, objectIntersectionOfK, objectUnionOfK,
     objectComplementOfK, objectOneOfK, objectSomeValuesFromK,
     objectAllValuesFromK, objectHasValueK, objectHasSelfK,
     objectMinCardinalityK, objectMaxCardinalityK, objectExactCardinalityK,
     dataSomeValuesFromK, dataAllValuesFromK, dataHasValueK,
     dataMinCardinalityK, dataMaxCardinalityK, dataExactCardinalityK]
