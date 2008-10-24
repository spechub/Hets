{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module defines all the data types for the functional style Syntax
of OWL 1.1.
It is modeled after the W3C document: <http://www.w3.org/Submission/2006/SUBM-owl11-owl_specification-20061219/>
-}

module OWL.AS where

import qualified Data.Map as Map

data QName = QN
  { namePrefix :: String
  -- ^ the name prefix part of a qualified name \"namePrefix:localPart\"
  , localPart :: String
  -- ^ the local part of a qualified name \"namePrefix:localPart\"
  , namespaceUri :: String
  -- ^ the associated namespace uri
  } deriving Show

nullQName :: QName
nullQName = QN "" "" ""

mkQName :: String -> QName
mkQName s = nullQName { localPart = s }

instance Eq QName where
    p == q = compare p q == EQ

instance Ord QName where
  compare(QN p1 l1 n1) (QN p2 l2 n2) =
      if null n1 then
          if null n2 then compare (p1, l1) (p2, l2) else LT
      else if null n2 then GT else compare (l1, n1) (l2, n2)

type URI = QName
type IRI = String
type URIreference = QName

-- | prefix -> localname
type Namespace = Map.Map String String

type AnnotationURI = URI
type OntologyURI = URI
type DatatypeURI = URI
type OwlClassURI = URI
type ObjectPropertyURI = URI
type DataPropertyURI = URI
type IndividualURI = URI
type ImportURI = URI

-- | Syntax of Ontologies
data Annotation =
    ExplicitAnnotation AnnotationURI Constant
                                     -- ^ ExplicitAnnotationByConstant
  | Label Constant     -- ^ LabelAnnotation
  | Comment Constant   -- ^ CommentAnnotation
  | Annotation AnnotationURI Entity  -- ^ AnnotationByEntity
    deriving (Show, Eq, Ord)

data OntologyFile = OntologyFile
  { namespaces :: Namespace
  , ontology :: Ontology
  } deriving (Show, Eq, Ord)

data Ontology = Ontology
  { uri :: OntologyURI
  , importsList :: [ImportURI]
  , annotationsList :: [Annotation]
  , axiomsList :: [Axiom]
  } deriving (Show, Eq, Ord)

type OntologyMap = Map.Map String OntologyFile

data EntityType =
    Datatype
  | OWLClassEntity
  | ObjectProperty
  | DataProperty
  | Individual
    deriving (Show, Eq, Ord)

-- | Syntax of Entities
data Entity = Entity EntityType URI deriving (Show, Eq, Ord)

type LexicalForm = String
type LanguageTag = String

-- | a lexical representation either with an "^^" URI (tyoed) or
-- an optional language tag starting with "\@" (untyped)
data Constant = Constant LexicalForm (Either URIreference LanguageTag)
    deriving (Show, Eq, Ord)

-- | Object and Data Property Expressions
type InverseObjectProperty = ObjectPropertyExpression

data ObjectPropertyExpression =
    OpURI ObjectPropertyURI
  | InverseOp InverseObjectProperty
    deriving (Show, Eq, Ord)

type DataPropertyExpression = DataPropertyURI

-- | Syntax of Data Range
data DatatypeFacet =
    LENGTH
  | MINLENGTH
  | MAXLENGTH
  | PATTERN
  | MININCLUSIVE
  | MINEXCLUSIVE
  | MAXINCLUSIVE
  | MAXEXCLUSIVE
  | TOTALDIGITS
  | FRACTIONDIGITS
    deriving (Show, Eq, Ord)

type RestrictionValue = Constant

data DataRange =
    DRDatatype DatatypeURI
  | DataComplementOf DataRange
  | DataOneOf [Constant] --  min. 1 constant
  | DatatypeRestriction DataRange [(DatatypeFacet, RestrictionValue)]
    deriving (Show, Eq, Ord)

-- | Syntax of Entity Annotations
type AnnotationsForAxiom = Annotation
type AnnotationsForEntity = Annotation

data EntityAnnotation =
    EntityAnnotation [AnnotationsForAxiom] Entity [AnnotationsForEntity]
    deriving (Show, Eq, Ord)

-- | Syntax of Classes
type Cardinality = Int

data Description =
    OWLClass OwlClassURI
  | ObjectUnionOf [Description]  --  min. 2 Descriptions
  | ObjectIntersectionOf [Description]  --  min. 2 Descriptions
  | ObjectComplementOf Description
  | ObjectOneOf [IndividualURI]  --  min. 1 Individual
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
    deriving (Show, Eq, Ord)

-- Axiom
type SubClass = Description
type SuperClass = Description

data SubObjectPropertyExpression =
    OPExpression ObjectPropertyExpression
  | SubObjectPropertyChain [ObjectPropertyExpression]
      -- ^ min. 2 ObjectPropertyExpression
    deriving (Show, Eq, Ord)

type SourceIndividualURI = IndividualURI
type TargetIndividualURI = IndividualURI
type TargetValue = Constant

data Axiom = -- Annotations can be ignored
    SubClassOf [Annotation] SubClass SuperClass
  | EquivalentClasses [Annotation] [Description] -- min. 2 desc.
  | DisjointClasses [Annotation] [Description] -- min. 2 desc.
  | DisjointUnion [Annotation] OwlClassURI [Description] -- min. 2 desc.
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
  | DataPropertyAssertion [Annotation] DataPropertyExpression SourceIndividualURI TargetValue
  | NegativeDataPropertyAssertion [Annotation] DataPropertyExpression SourceIndividualURI TargetValue
  | Declaration [Annotation] Entity
  | EntityAnno EntityAnnotation
    deriving (Show, Eq, Ord)

emptyOntologyFile :: OntologyFile
emptyOntologyFile = OntologyFile Map.empty emptyOntology

emptyOntology :: Ontology
emptyOntology = Ontology nullQName [] [] []

isEmptyOntologyFile :: OntologyFile -> Bool
isEmptyOntologyFile (OntologyFile ns onto) =
    Map.null ns && isEmptyOntology onto

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology (QN _ l n) annoList impList axioms) =
    null l && null n && null annoList && null impList && null axioms
