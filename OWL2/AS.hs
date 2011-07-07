{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Common datatypes for the Functional and Manchester Syntaxes of OWL 2

References:
 <http://www.w3.org/TR/2009/REC-owl2-syntax-20091027/#Functional-Style_Syntax>
 <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.AS where

import Common.Keywords
import Common.Id (GetRange)

import OWL2.Keywords
import OWL2.ColonKeywords
import qualified Data.Map as Map

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
  } deriving Show

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
  compare (QN p1 l1 b1 n1) (QN p2 l2 b2 n2) = case (n1, n2) of
    ([], []) -> compare (b1, p1, l1) (b2, p2, l2)
    ([], _) -> LT
    (_, []) -> GT
    _ -> compare (b1, l1, n1) (b2, l2, n2)

type IRIreference = QName
type IRI = QName

-- | prefix -> localname
type PrefixMap = Map.Map String String

type LexicalForm = String
type LanguageTag = String
type ImportIRI = IRI
type OntologyIRI = IRI
type Class = IRI
type Datatype = IRI
type ObjectProperty = IRI
type DataProperty = IRI
type AnnotationProperty = IRI
type NamedIndividual = IRI
type Individual = IRI

-- * LITERALS

data TypedOrUntyped = Typed Datatype | Untyped (Maybe LanguageTag)
    deriving (Show, Eq, Ord)

data Literal = Literal LexicalForm TypedOrUntyped
    deriving (Show, Eq, Ord)

cTypeS :: String
cTypeS = "^^"

-- * PROPERTY EXPRESSIONS

type InverseObjectProperty = ObjectPropertyExpression

data ObjectPropertyExpression = ObjectProp ObjectProperty
  | ObjectInverseOf InverseObjectProperty
        deriving (Show, Eq, Ord)

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

-- * DATA RANGES

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
        = DataType Datatype [(ConstrainingFacet, RestrictionValue)]
        | DataJunction JunctionType [DataRange]
          -- at least two elements in the list
        | DataComplementOf DataRange
        | DataOneOf [Literal]   -- at least one element in the list
        deriving (Show, Eq, Ord)

data JunctionType = UnionOf | IntersectionOf deriving (Show, Eq, Ord)

type ConstrainingFacet = IRI
type RestrictionValue = Literal

-- * CLASS EXPERSSIONS

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
    deriving (Show, Eq, Ord)

data ClassExpression =
    Expression Class
  | ObjectJunction JunctionType [ClassExpression]  -- min. 2 ClassExpressions
  | ObjectComplementOf ClassExpression
  | ObjectOneOf [Individual]  -- min. 1 Individual
  | ObjectValuesFrom QuantifierType ObjectPropertyExpression ClassExpression
  | ObjectHasValue ObjectPropertyExpression Individual
  | ObjectHasSelf ObjectPropertyExpression
  | ObjectCardinality (Cardinality ObjectPropertyExpression ClassExpression)
  | DataValuesFrom QuantifierType
       DataPropertyExpression [DataPropertyExpression] DataRange
  | DataHasValue DataPropertyExpression Literal
  | DataCardinality (Cardinality DataPropertyExpression DataRange)
    deriving (Show, Eq, Ord)

-- * ANNOTATIONS

data Annotation = Annotation [Annotation] AnnotationProperty AnnotationValue
  deriving (Show, Eq, Ord)

data AnnotationValue
        = AnnValue IRI
        | AnnValLit Literal
          deriving (Show, Eq, Ord)

-- * ENTITIES

data Entity = Entity EntityType IRI deriving (Show, Eq, Ord)

instance GetRange Entity

data EntityType =
    Datatype
  | Class
  | ObjectProperty
  | DataProperty
  | AnnotationProperty
  | NamedIndividual
    deriving (Enum, Bounded, Show, Read, Eq, Ord)

showEntityType :: EntityType -> String
showEntityType e = case e of
    Datatype -> datatypeC
    Class -> classC
    ObjectProperty -> objectPropertyC
    DataProperty -> dataPropertyC
    AnnotationProperty -> annotationPropertyC
    NamedIndividual -> individualC

entityTypes :: [EntityType]
entityTypes = [minBound .. maxBound]

-- * CASES

type SourceIndividual = Individual
type TargetIndividual = Individual
type TargetValue = Literal

data EquivOrDisjoint = Equivalent | Disjoint
    deriving (Show, Eq, Ord)

showEquivOrDisjoint :: EquivOrDisjoint -> String
showEquivOrDisjoint ed = case ed of
    Equivalent -> equivalentToC
    Disjoint -> disjointWithC

data DomainOrRange = ADomain | ARange deriving (Show, Eq, Ord)

showDomainOrRange :: DomainOrRange -> String
showDomainOrRange dr = case dr of
    ADomain -> domainC
    ARange -> rangeC

data Relation =
    EDRelation EquivOrDisjoint
  | SubPropertyOf
  | InverseOf
  | SubClass
  | Types
  | DRRelation DomainOrRange
  | SDRelation SameOrDifferent
    deriving (Show, Eq, Ord)

showRelation :: Relation -> String
showRelation r = case r of
    EDRelation ed -> showEquivOrDisjoint ed
    SubPropertyOf -> subPropertyOfC
    InverseOf -> inverseOfC
    SubClass -> subClassOfC
    Types -> typesC
    DRRelation dr -> showDomainOrRange dr
    SDRelation sd -> showSameOrDifferent sd

getDR :: Relation -> DomainOrRange
getDR r = case r of
    DRRelation dr -> dr
    _ -> error "not domain or range"

getED :: Relation -> EquivOrDisjoint
getED r = case r of
    EDRelation ed -> ed
    _ -> error "not domain or range"

getSD :: Relation -> SameOrDifferent
getSD s = case s of
    SDRelation sd -> sd
    _ -> error "not same or different"

data DataDomainOrRange = DataDomain ClassExpression | DataRange DataRange
    deriving (Show, Eq, Ord)

data Character =
    Functional
  | InverseFunctional
  | Reflexive
  | Irreflexive
  | Symmetric
  | Asymmetric
  | Antisymmetric
  | Transitive
    deriving (Enum, Bounded, Show, Eq, Ord)

data SameOrDifferent = Same | Different deriving (Show, Eq, Ord)

showSameOrDifferent :: SameOrDifferent -> String
showSameOrDifferent sd = case sd of
    Same -> sameAsC
    Different -> differentFromC

data PositiveOrNegative = Positive | Negative deriving (Show, Eq, Ord)
