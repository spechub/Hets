{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(deriving Typeable)

This module defines all the data types for the functional style Syntax
of OWL 2
It is modeled after the W3C document:
<http://www.w3.org/TR/2009/REC-owl2-syntax-20091027/#Functional-Style_Syntax>
-}

module OWL2.AS where

import Common.Keywords
import Common.Id (GetRange)

import OWL.Keywords
import OWL.ColonKeywords
import qualified Data.Map as Map
import Data.Typeable

{- | full or abbreviated IRIs with a possible uri for the prefix
     or a local part following a hash sign -}
data QName = QN
  { namePrefix :: String
  -- ^ the name prefix part of a qualified name \"namePrefix:localPart\"
  , localPart :: String
  -- ^ the local part of a qualified name \"namePrefix:localPart\"
  , isFullIri :: Bool
  , namespaceUri :: String
  -- ^ the associated namespace uri (not printed)
  } deriving (Typeable, Show)

showQN :: QName -> String
showQN q = (if isFullIri q then showQI else showQU) q

-- | show QName as abbreviated iri
showQU :: QName -> String
showQU (QN pre local _ _) =
    if null pre then local else pre ++ ":" ++ local

-- | show QName in ankle brackets as full iris
showQI :: QName -> String
showQI = ('<' :) . (++ ">") . showQU

nullQName :: QName
nullQName = QN "" "" False ""

dummyQName :: QName
dummyQName = QN "http" "//www.dfki.de/sks/hets/ontology/unamed" True ""

mkQName :: String -> QName
mkQName s = nullQName { localPart = s }

instance Eq QName where
    p == q = compare p q == EQ

instance Ord QName where
  compare (QN p1 l1 b1 n1) (QN p2 l2 b2 n2) =
    if null n1 then
      if null n2 then compare (b1, p1, l1) (b2, p2, l2) else LT
    else if null n2 then GT else compare (b1, l1, n1) (b2, l2, n2)

type IRIreference = QName
type IRI = QName

-- | prefix -> localname
type PrefixMap = Map.Map String String

type NodeID = IRI
type LexicalForm = String
type LanguageTag = String
type PrefixName = String
type ImportIRI = IRI
type OntologyIRI = IRI
type Class = IRI
type Datatype = IRI
type ObjectProperty = IRI
type DataProperty = IRI
type AnnotationProperty = IRI
type NamedIndividual = IRI
type Individual = IRI

------------------------
-- ONTOLOGIES SYNTAX
------------------------

data OntologyFile = OntologyFile
  { prefixName :: PrefixMap
  , ontology :: Ontology
  } deriving (Typeable, Show, Eq, Ord)

instance GetRange OntologyFile

data Ontology = Ontology
  { uri :: OntologyIRI
  , importsList :: [ImportIRI]
  , annotationsList :: [Annotation]
  , axiomsList :: [Axiom]
  } deriving (Typeable, Show, Eq, Ord)

type OntologyMap = Map.Map String OntologyFile

------------------------
-- SYMBOL ITEMS FOR HETS
------------------------

data SymbItems = SymbItems (Maybe EntityType) [IRI]
    deriving (Typeable, Show, Eq)

data SymbMapItems = SymbMapItems (Maybe EntityType) [(IRI, Maybe IRI)]
    deriving (Typeable, Show, Eq)

-- | raw symbols
data RawSymb = ASymbol Entity | AnUri IRI deriving (Typeable, Show, Eq, Ord)

-------------------------
-- LITERALS
-------------------------

data TypedOrUntyped = Typed Datatype | Untyped (Maybe LanguageTag)
    deriving (Typeable, Show, Eq, Ord)

data Literal = Literal LexicalForm TypedOrUntyped
    deriving (Typeable, Show, Eq, Ord)

cTypeS :: String
cTypeS = "^^"

-- | a lexical representation either with an "^^" URI (typed) or
-- an optional language tag starting with "\@" (untyped)

--------------------------
-- PROPERTY EXPRESSIONS
--------------------------

type InverseObjectProperty = ObjectPropertyExpression

data ObjectPropertyExpression = ObjectProp ObjectProperty | ObjectInverseOf InverseObjectProperty
	deriving (Typeable, Show, Eq, Ord)

type DataPropertyExpression = DataProperty

-- | data type strings (some are not listed in the grammar)
datatypeKeys :: [String]
datatypeKeys =
  [ booleanS
  , dATAS
  , decimalS
  , floatS
  , integerS
  , negativeIntegerS
  , nonNegativeIntegerS
  , nonPositiveIntegerS
  , positiveIntegerS
  , stringS
  , universalS
  ]

--------------------------
-- DATA RANGES
--------------------------

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
    deriving (Typeable, Show, Eq, Ord)

showFacet :: DatatypeFacet -> String
showFacet df = case df of
    LENGTH -> lengthS
    MINLENGTH -> minLengthS
    MAXLENGTH -> maxLengthS
    PATTERN -> patternS
    MININCLUSIVE -> lessEq
    MINEXCLUSIVE -> lessS
    MAXINCLUSIVE -> greaterEq
    MAXEXCLUSIVE -> greaterS
    TOTALDIGITS -> digitsS
    FRACTIONDIGITS -> fractionS

data DataRange 
	= DataType Datatype
	| DataJunction JunctionType [DataRange]  -- at least two elements in the list
	| DataComplementOf DataRange
	| DataOneOf [Literal]	-- at least one element in the list
	| DatatypeRestriction Datatype [(ConstrainingFacet, RestrictionValue)]	-- at least one element in the list
	deriving (Typeable, Show, Eq, Ord)

data JunctionType = UnionOf | IntersectionOf deriving (Show, Eq, Ord)

type ConstrainingFacet = IRI
type RestrictionValue = Literal

---------------------------
-- CLASS EXPERSSIONS
---------------------------

data QuantifierType = AllValuesFrom | SomeValuesFrom deriving (Show, Eq, Ord)

showQuantifierType :: QuantifierType -> String
showQuantifierType ty = case ty of
    AllValuesFrom -> onlyS
    SomeValuesFrom -> someS

data CardinalityType = MinCardinality | MaxCardinality | ExactCardinality
    deriving (Show, Eq, Ord)

showCardinalityType :: CardinalityType -> String
showCardinalityType ty = case ty of
    MinCardinality -> minS
    MaxCardinality -> maxS
    ExactCardinality -> exactlyS

data Cardinality a b = Cardinality CardinalityType Int a (Maybe b)
    deriving (Typeable, Show, Eq, Ord)

data ClassExpression =
    Expression Class
  | ObjectJunction JunctionType [ClassExpression]  -- min. 2 ClassExpressions
  | ObjectComplementOf ClassExpression
  | ObjectOneOf [Individual]  -- min. 1 Individual
  | ObjectValuesFrom QuantifierType ObjectPropertyExpression ClassExpression
  | ObjectHasValue ObjectPropertyExpression Individual
  | ObjectHasSelf ObjectPropertyExpression
  | ObjectCardinality (Cardinality ObjectPropertyExpression ClassExpression)
  | DataValuesFrom 
	     QuantifierType DataPropertyExpression [DataPropertyExpression] DataRange
  | DataHasValue DataPropertyExpression Literal
  | DataCardinality (Cardinality DataPropertyExpression DataRange)
    deriving (Typeable, Show, Eq, Ord)

-------------------
-- ANNOTATIONS
-------------------

data Annotation = Annotation [Annotation] AnnotationProperty AnnotationValue
	  deriving (Typeable, Show, Eq, Ord)

data AnnotationAxiom 
	= AnnotationAssertion [Annotation] IRI
	| SubAnnotationPropertyOf [Annotation] AnnotationProperty AnnotationProperty
	| AnnotationPropertyDomainOrRange AnnotationDomainOrRange [Annotation] AnnotationProperty IRI
	deriving (Typeable, Show, Eq, Ord)

data AnnotationDomainOrRange = AnnDomain | AnnRange deriving (Show, Eq, Ord)

showAnnDomainOrRange :: AnnotationDomainOrRange -> String
showAnnDomainOrRange dr = case dr of
    AnnDomain -> domainC
    AnnRange -> rangeC

data AnnotationValue 
	= AnnValue IRI
	| AnnValLit Literal
	  deriving (Typeable, Show, Eq, Ord)

---------------------
-- AXIOMS
---------------------

--Entities

data EntityType =
    Datatype
  | Class
  | ObjectProperty
  | DataProperty
  | AnnotationProperty
  | NamedIndividual
    deriving (Typeable, Enum, Bounded, Show, Read, Eq, Ord)

-- | Syntax of Entities
data Entity = Entity EntityType IRI deriving (Typeable, Show, Eq, Ord)

instance GetRange Entity

entityTypes :: [EntityType]
entityTypes = [minBound .. maxBound]

type SourceIndividual = Individual
type TargetIndividual = Individual
type TargetValue = Literal

data Axiom = -- Annotations can be ignored
    PlainAxiom [Annotation] PlainAxiom
  | EntityAnno AnnotationAxiom
    deriving (Typeable, Show, Eq, Ord)

instance GetRange Axiom

data EquivOrDisjoint = Equivalent | Disjoint deriving (Show, Eq, Ord)

showEquivOrDisjoint :: EquivOrDisjoint -> String
showEquivOrDisjoint ed = case ed of
    Equivalent -> equivalentToC
    Disjoint -> disjointWithC

data ObjDomainOrRange = ObjDomain | ObjRange deriving (Show, Eq, Ord)

showObjDomainOrRange :: ObjDomainOrRange -> String
showObjDomainOrRange dr = case dr of
    ObjDomain -> domainC
    ObjRange -> rangeC

data DataDomainOrRange = DataDomain ClassExpression | DataRange DataRange
    deriving (Typeable, Show, Eq, Ord)

data Character =
    Functional
  | InverseFunctional
  | Reflexive
  | Irreflexive
  | Symmetric
  | Asymmetric
  | Antisymmetric
  | Transitive
    deriving (Typeable, Enum, Bounded, Show, Eq, Ord)

data SameOrDifferent = Same | Different deriving (Show, Eq, Ord)

showSameOrDifferent :: SameOrDifferent -> String
showSameOrDifferent sd = case sd of
    Same -> sameAsC
    Different -> differentFromC

data PositiveOrNegative = Positive | Negative deriving (Show, Eq, Ord)

data Assertion a b = Assertion a PositiveOrNegative SourceIndividual b
    deriving (Typeable, Show, Eq, Ord)

data PlainAxiom =
    SubClassOf SubClass SuperClass
  | EquivOrDisjointClasses EquivOrDisjoint [ClassExpression] -- min. 2 desc.
  | DisjointUnion Class [ClassExpression] -- min. 2 desc.
  | SubObjectPropertyOf SubObjectPropertyExpression ObjectPropertyExpression
  | EquivOrDisjointObjectProperties EquivOrDisjoint [ObjectPropertyExpression]  -- min. 2  ObjectPropertyExpression
  | ObjectPropertyDomainOrRange ObjDomainOrRange ObjectPropertyExpression ClassExpression
  | InverseObjectProperties ObjectPropertyExpression ObjectPropertyExpression
  | ObjectPropertyCharacter Character ObjectPropertyExpression
  | SubDataPropertyOf DataPropertyExpression DataPropertyExpression
  | EquivOrDisjointDataProperties EquivOrDisjoint [DataPropertyExpression] -- min. 2 DataPropertyExpressions
  | DataPropertyDomainOrRange DataDomainOrRange DataPropertyExpression
  | FunctionalDataProperty DataPropertyExpression
  | SameOrDifferentIndividual SameOrDifferent [Individual] -- min. 2 ind.
  | ClassAssertion ClassExpression Individual 	-- arguments are reversed from OWL-1
  | ObjectPropertyAssertion (Assertion ObjectPropertyExpression TargetIndividual)
  | DataPropertyAssertion (Assertion DataPropertyExpression TargetValue)
  | Declaration Entity
  | DatatypeDefinition Datatype DataRange
  | HasKey ClassExpression [ObjectPropertyExpression] [DataPropertyExpression]
    deriving (Typeable, Show, Eq, Ord)

type SubClass = ClassExpression
type SuperClass = ClassExpression

data SubObjectPropertyExpression 
  = OPExpression ObjectPropertyExpression
  | SubObjectPropertyChain [ObjectPropertyExpression] -- min. 2 ObjectPropertyExpression
    deriving (Typeable, Show, Eq, Ord)

---------------------
-- ONTOLOGY FILES
---------------------
emptyOntologyFile :: OntologyFile
emptyOntologyFile = OntologyFile Map.empty emptyOntology

emptyOntology :: Ontology
emptyOntology = Ontology nullQName [] [] []

isEmptyOntologyFile :: OntologyFile -> Bool
isEmptyOntologyFile (OntologyFile ns onto) =
    Map.null ns && isEmptyOntology onto

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology (QN _ l _ n) annoList impList axioms) =
    null l && null n && null annoList && null impList && null axioms
