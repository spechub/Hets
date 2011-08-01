{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

OWL 2 Functional Syntax constructs

References:
 <http://www.w3.org/TR/2009/REC-owl2-syntax-20091027/#Functional-Style_Syntax>
 <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.AS where

import Common.Id
import Common.Keywords

import OWL2.ColonKeywords
import OWL2.Keywords

import Data.List
import qualified Data.Map as Map

data IRIType = Full | Abbreviated | NodeID
    deriving (Show, Eq, Ord)

{- | full or abbreviated IRIs with a possible uri for the prefix
     or a local part following a hash sign -}
data QName = QN
  { namePrefix :: String
  -- ^ the name prefix part of a qualified name \"namePrefix:localPart\"
  , localPart :: String
  -- ^ the local part of a qualified name \"namePrefix:localPart\"
  , iriType :: IRIType
  , expandedIRI :: String
  -- ^ the associated namespace uri (not printed)
  , iriPos :: Range
  } deriving Show

instance Eq QName where
    p == q = compare p q == EQ

instance Ord QName where
  compare (QN p1 l1 b1 n1 _) (QN p2 l2 b2 n2 _) =
    if null n1 || null n2 then compare (b1, p1, l1) (b2, p2, l2) else
      compare n1 n2 -- compare fully expanded names only

instance GetRange QName where
  getRange = iriPos

showQN :: QName -> String
showQN q = (if iriType q /= Abbreviated then showQI else showQU) q

-- | show QName as abbreviated iri
showQU :: QName -> String
showQU (QN pre local _ _ _) =
    if null pre then local else pre ++ ":" ++ local

-- | show QName in ankle brackets as full iris
showQI :: QName -> String
showQI = ('<' :) . (++ ">") . showQU

nullQName :: QName
nullQName = QN "" "" Abbreviated "" nullRange

dummyQName :: QName
dummyQName =
  QN "http" "//www.dfki.de/sks/hets/ontology/unamed" Full "" nullRange

mkQName :: String -> QName
mkQName s = nullQName { localPart = s }

setQRange :: Range -> QName -> QName
setQRange r q = q { iriPos = r }

setPrefix :: String -> QName -> QName
setPrefix s q = q { namePrefix = s }

setReservedPrefix :: QName -> QName
setReservedPrefix iri
    | isDatatypeKey iri = setPrefix "xsd" iri
    | isThing iri = setPrefix "owl" iri
    | otherwise = iri

setFull :: QName -> QName
setFull q = q {iriType = Full}

type IRI = QName

-- | checks if an IRI is an anonymous individual
isAnonymous :: IRI -> Bool
isAnonymous iri = iriType iri == NodeID

isThing :: IRI -> Bool
isThing u = elem (localPart u) ["Thing", "Nothing"] &&
                elem (namePrefix u) ["", "owl"]

-- | checks if a string (bound to be localPart of an IRI) contains "://"
cssIRI :: String -> IRIType
cssIRI iri = if isInfixOf "://" iri then Full else Abbreviated

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

data EquivOrDisjoint = Equivalent | Disjoint
    deriving (Show, Eq, Ord)

showEquivOrDisjoint :: EquivOrDisjoint -> String
showEquivOrDisjoint ed = case ed of
    Equivalent -> equivalentToC
    Disjoint -> disjointWithC

data DomainOrRange = ADomain | ARange
    deriving (Show, Eq, Ord)

showDomainOrRange :: DomainOrRange -> String
showDomainOrRange dr = case dr of
    ADomain -> domainC
    ARange -> rangeC

data SameOrDifferent = Same | Different
    deriving (Show, Eq, Ord)

showSameOrDifferent :: SameOrDifferent -> String
showSameOrDifferent sd = case sd of
    Same -> sameAsC
    Different -> differentFromC

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

getED :: Relation -> EquivOrDisjoint
getED r = case r of
    EDRelation ed -> ed
    _ -> error "not domain or range"

getDR :: Relation -> DomainOrRange
getDR r = case r of
    DRRelation dr -> dr
    _ -> error "not domain or range"

getSD :: Relation -> SameOrDifferent
getSD s = case s of
    SDRelation sd -> sd
    _ -> error "not same or different"

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

data PositiveOrNegative = Positive | Negative
    deriving (Show, Eq, Ord)

data QuantifierType = AllValuesFrom | SomeValuesFrom
    deriving (Show, Eq, Ord)

showQuantifierType :: QuantifierType -> String
showQuantifierType ty = case ty of
    AllValuesFrom -> onlyS
    SomeValuesFrom -> someS

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

isDatatypeKey :: IRI -> Bool
isDatatypeKey u =
  elem (localPart u) datatypeKeys && elem (namePrefix u) ["", "xsd"]

data DatatypeType = OWL2Int | OWL2String | OWL2Bool | Other
    deriving (Show, Eq, Ord)

datatypeType :: IRI -> DatatypeType
datatypeType iri =
    let lp = localPart iri
    in case isDatatypeKey iri of
        True
            | lp == booleanS -> OWL2Bool
            | lp `elem` [integerS, negativeIntegerS, nonNegativeIntegerS,
                nonPositiveIntegerS, positiveIntegerS] -> OWL2Int
            | lp == stringS -> OWL2String
            | otherwise -> Other
        False -> Other

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

data CardinalityType = MinCardinality | MaxCardinality | ExactCardinality
    deriving (Show, Eq, Ord)

showCardinalityType :: CardinalityType -> String
showCardinalityType ty = case ty of
    MinCardinality -> minS
    MaxCardinality -> maxS
    ExactCardinality -> exactlyS

data Cardinality a b = Cardinality CardinalityType Int a (Maybe b)
    deriving (Show, Eq, Ord)

data JunctionType = UnionOf | IntersectionOf
    deriving (Show, Eq, Ord)

type ConstrainingFacet = IRI
type RestrictionValue = Literal

-- * ENTITIES

data Entity = Entity EntityType IRI deriving (Show, Eq, Ord)

instance GetRange Entity where
  getRange (Entity _ iri) = iriPos iri

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

-- * DATA RANGES

data DataRange
  = DataType Datatype [(ConstrainingFacet, RestrictionValue)]
  | DataJunction JunctionType [DataRange]
  | DataComplementOf DataRange
  | DataOneOf [Literal]
    deriving (Show, Eq, Ord)

-- * CLASS EXPERSSIONS

data ClassExpression =
    Expression Class
  | ObjectJunction JunctionType [ClassExpression]
  | ObjectComplementOf ClassExpression
  | ObjectOneOf [Individual]
  | ObjectValuesFrom QuantifierType ObjectPropertyExpression ClassExpression
  | ObjectHasValue ObjectPropertyExpression Individual
  | ObjectHasSelf ObjectPropertyExpression
  | ObjectCardinality (Cardinality ObjectPropertyExpression ClassExpression)
  | DataValuesFrom QuantifierType DataPropertyExpression DataRange
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
