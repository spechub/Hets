{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module defines all the data types for the Abstract Syntax of OWL_DL.
It is modeled after the W3C document: <http://www.w3.org/TR/owl-semantics/>
-}

module OWL_DL.OWL11.FFS (module OWL_DL.OWL11.FFS, QName(..)) where

import qualified Data.Map as Map
import Text.XML.HXT.DOM.TypeDefs (mkName)
import Text.XML.HXT.DOM.XmlTreeTypes
    (QName(QN),namePrefix,localPart,namespaceUri)


data URI = Full-IRI URIreference 
         | Abbreviated-IRI IRI
type IRI = String 
type URIreference = QName
type Namespace = Map.Map String String      -- ^ prefix -> localname

type AnnotationURI = URI
type OntologyURI = URI
type DatatypeURI = URI
type OwlClassURI = URI
type ObjectPropertyURI = URI
type DataPropertyURI = URI
type IndividualURI = URI 
type ImportURI = URI


-- Ontologies
data Annotation = -- AnnotationByConstant 
                  ExplicitAnnotation AnnotationURI Constant 
                                     -- ExplicitAnnotationByConstant
                | Label Constant     -- LabelAnnotation
                | Comment Constant   --CommentAnnotation
                | Annotation AnnotationURI Entity  -- AnnotationByEntity

data OntologyFile = OntologyFile Namespace Ontology
data Ontology = Ontology OntologyURI [ImportURI] [Annotation] [Axiom]

-- Entities
data Entity = Datatype DatatypeURI
            | OwlClass OwlClassURI
            | ObjectProperty ObjectPropertyURI
            | DataProperty DataPropertyURI
            | Individual IndividualURI

type LexicalForm = String
type LanguageTag = String
data Constant = TypedConstant  (LexicalForm, URIreference)
    -- ^ consist of a lexical representatoin and a URI with ^^ .
              | UntypedConstant  (LexicalForm, LanguageTag)
    -- ^ Unicode string in Normal Form C and an optional language tag with @

-- Object and Data Property Expressions
type InverseObjectProperty = ObjectPropertyExpression 
data ObjectPropertyExpression = OpURI ObjectPropertyURI 
                              | InverseOp InverseObjectProperty 
type DataPropertyExpression = DataPropertyURI 


-- Data Range
data DatatypeFacet = Length
                   | MinLength 
                   | MaxLength
                   | Pattern
                   | MinInclusive
                   | MinExclusive
                   | MaxInclusive
                   | MaxExclusive
                   | TotalDigits 
                   | FractionDigits
type RestrictionValue = Constant
e 
data DataRange = Datatype DatatypeURI 
               | DataComplementOf DataRange
               | DataOneOf [Constant] -- min. 1 constant
               | DatatypeRestriction DataRange DatatypeFacet RestrictionValue

-- Entity Annotations
type AnnotationsForAxiom = Annotation
type AnnotationsForEntity = Annotation
data EntityAnnotation = EntityAnnotation [AnnotationsForAxiom] Entity 
                                         [AnnotationsForEntity]

-- Classes
type Cardinality = Int
data Description = OWLClass OwlClassURI
                 | ObjectUnionOf [Description]  -- min. 2 Descriptions
                 | ObjectIntersectionOf [Description]  -- min. 2 Descriptions
                 | ObjectComplementOf Description
                 | ObjectOneOf [IndividualURI]  -- min. 1 Individual
                 | ObjectAllValuesFrom ObjectPropertyExpression Description 
                 | ObjectSomeValuesFrom ObjectPropertyExpression Description 
                 | ObjectExistsSelf ObjectPropertyExpression
                 | ObjectHasValue ObjectPropertyExpression IndividualURI
                 | ObjectMinCardinality Cardinality ObjectPropertyExpression (Maybe Description)
                 | ObjectMaxCardinality Cardinality ObjectPropertyExpression (Maybe Description)
                 | ObjectExactCardinality Cardinality ObjectPropertyExpression (Maybe Description)
                 | DataAllValuesFrom DataPropertyExpression [DataPropertyExpression] DataRange 
                 | DataSomeValuesFrom DataPropertyExpression [DataPropertyExpression] DataRange
                 | DataHasValue DataPropertyExpression Constant
                 | DataMinCardinality Cardinality DataPropertyExpression (Maybe DataRange)
                 | DataMaxCardinality Cardinality DataPropertyExpression (Maybe DataRange)
                 | DataExactCardinality Cardinality DataPropertyExpression (Maybe DataRange)


-- Axiom
type SubClass = Description
type SuperClass = Description
data SubObjectPropertyExpression 
    = OPExpression ObjectPropertyExpression 
    | SubObjectPropertyChain [ObjectPropertyExpression]  -- min. 2 ObjectPropertyExpression
type SourceIndividualURI = IndividualURI
type TargetIndividualURI = IndividualURI
type TargetValue := Constant


data Axiom =  -- ClassAxiom
             SubClassOf [Annotation] SubClass SuperClass
           | EquivalentClasses [Annotation] [Description] -- min. 2 desc.
           | DisjointClasses [Annotation] [Description] -- min. 2 desc.
           | DisjointUnion [Annotation] OwlClassURI [Description] -- min. 2 desc.
           -- ObjectPropertyAxiom 
           | SubObjectPropertyOf [Annotation] SubObjectPropertyExpression ObjectPropertyExpression
           | EquivalentObjectProperties [Annotation] [ObjectPropertyExpression]
                                  -- min. 2  ObjectPropertyExpression
           | DisjointObjectProperties [Annotation] [ObjectPropertyExpression]
                                  -- min. 2  ObjectPropertyExpression
           | ObjectPropertyDomain [Annotation] ObjectPropertyExpression Description
           | ObjectPropertyRange [Annotation] ObjectPropertyExpression Description
           | InverseObjectProperties [Annotation] ObjectPropertyExpression ObjectPropertyExpression
           | FunctionalObjectProperty [Annotation] ObjectPropertyExpression
           | InverseFunctionalObjectProperty [Annotation] ObjectPropertyExpression 
           | ReflexiveObjectProperty [Annotation] ObjectPropertyExpression
           | IrreflexiveObjectProperty [Annotation] ObjectPropertyExpression
           | SymmetricObjectProperty [Annotation] ObjectPropertyExpression
           | AntisymmetricObjectProperty [Annotation] ObjectPropertyExpression
           | TransitiveObjectProperty [Annotation] ObjectPropertyExpression
           -- DataPropertyAxiom 
           | SubDataPropertyOf [Annotation] DataPropertyExpression DataPropertyExpression
           | EquivalentDataProperties [Annotation] [DataPropertyExpression]
                                  -- min. 2 DataPropertyExpressions
           | DisjointDataProperties [Annotation] [DataPropertyExpression]
                                  -- min. 2 DataPropertyExpressions
           | DataPropertyDomain [Annotation] DataPropertyExpression Description
           | DataPropertyRange [Annotation] DataPropertyExpression DataRange
           | FunctionalDataProperty [Annotation] DataPropertyExpression
           -- Fact
           | SameIndividual [Annotation] [IndividualURI]  -- min. 2 ind.
           | DifferentIndividuals [Annotation] [IndividualURI]  -- min. 2 ind.
           | ClassAssertion [Annotation] IndividualURI Description 
           | ObjectPropertyAssertion [Annotation] ObjectPropertyExpression SourceIndividualURI TargetIndividualURI 
           | NegativeObjectPropertyAssertion [Annotation] ObjectPropertyExpression SourceIndividualURI TargetIndividualURI
           | DataPropertyAssertion [Annotation]DataPropertyExpression SourceIndividualURI TargetValue 
           | NegativeDataPropertyAssertion [Annotation] DataPropertyExpression SourceIndividualURI TargetValue
           | Declaration [Annotation] Entity 
           | EntityAnno EntityAnnotation 


emptyOntologyFile :: OntologyFile
emptyOntologyFile = OntologyFile Map.empty emptyOntology

emptyOntology :: Ontology
emptyOntology = Ontology (Full-IRI (mkName "")) [] [] []

-- check if QName is empty
isEmptyQN :: QName -> Bool
isEmptyQN (QN a b c) =
    (null a) && (null b) && (null c)
