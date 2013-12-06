{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, Felix Gabriel Mance
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
import OWL2.ColonKeywords
import OWL2.Keywords

import Data.Char (intToDigit)
import Data.List
import Data.Maybe
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

qNameRange :: QName -> [Pos]
qNameRange q = let Range rs = iriPos q in case rs of
  [p] -> let
    p0 = if iriType q == Full then incSourceColumn p (-1) else p
    in tokenRange $ Token (showQN q) $ Range [p0]
  _ -> rs

instance GetRange QName where
  getRange = iriPos
  rangeSpan = qNameRange

showQN :: QName -> String
showQN q = (if iriType q == Full then showQI else showQU) q

-- | show QName as abbreviated iri
showQU :: QName -> String
showQU (QN pre local _ _ _) =
    if null pre then local else pre ++ ":" ++ local

-- | show QName in ankle brackets as full iris
showQI :: QName -> String
showQI = ('<' :) . (++ ">") . showQU

nullQName :: QName
nullQName = QN "" "" Abbreviated "" nullRange

isNullQName :: QName -> Bool
isNullQName qn = case qn of
    QN "" "" _ "" _ -> True
    _ -> False

dummyQName :: QName
dummyQName =
  QN "http" "//www.dfki.de/sks/hets/ontology/unamed" Full
            "http://www.dfki.de/sks/hets/ontology/unamed" nullRange

mkQName :: String -> QName
mkQName s = nullQName { localPart = s }

setQRange :: Range -> QName -> QName
setQRange r q = q { iriPos = r }

setPrefix :: String -> QName -> QName
setPrefix s q = q { namePrefix = s }

setFull :: QName -> QName
setFull q = q {iriType = Full}

type IRI = QName

-- | checks if an IRI is an anonymous individual
isAnonymous :: IRI -> Bool
isAnonymous iri = iriType iri == NodeID || namePrefix iri == "_"

-- | checks if a string (bound to be localPart of an IRI) contains \":\/\/\"
cssIRI :: String -> IRIType
cssIRI iri = if isInfixOf "://" iri then Full else Abbreviated

-- | prefix -> localname
type PrefixMap = Map.Map String String

predefPrefixes :: PrefixMap
predefPrefixes = Map.fromList
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
      , ("", showQU dummyQName ++ "#") ]

type LexicalForm = String
type LanguageTag = String
type ImportIRI = IRI
type OntologyIRI = IRI
type Class = IRI
type Datatype = IRI
type ObjectProperty = IRI
type DataProperty = IRI
type AnnotationProperty = IRI
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

-- * Predefined IRI checkings

isThing :: IRI -> Bool
isThing = isOWLPredef predefClass

isPredefObjProp :: IRI -> Bool
isPredefObjProp = isOWLPredef predefObjProp

isPredefDataProp :: IRI -> Bool
isPredefDataProp = isOWLPredef predefDataProp

isPredefRDFSAnnoProp :: IRI -> Bool
isPredefRDFSAnnoProp = checkPredef predefRDFSAnnoProps "rdfs"

isPredefOWLAnnoProp :: IRI -> Bool
isPredefOWLAnnoProp = isOWLPredef predefOWLAnnoProps

isPredefAnnoProp :: IRI -> Bool
isPredefAnnoProp iri = isPredefOWLAnnoProp iri || isPredefRDFSAnnoProp iri

isPredefPropOrClass :: IRI -> Bool
isPredefPropOrClass iri = isPredefAnnoProp iri || isPredefDataProp iri
    || isPredefObjProp iri || isThing iri

predefIRIs :: [IRI]
predefIRIs = map (setPrefix "xsd" . mkQName) xsdKeys
    ++ map (setPrefix "owl" . mkQName) owlNumbers
    ++ [setPrefix "rdf" (mkQName rdfsLiteral),
        setPrefix "rdfs" $ mkQName xmlLiteral]

isDatatypeKey :: IRI -> Bool
isDatatypeKey = not . null . isDatatypeKeyAux

isDatatypeKeyAux :: IRI -> [(String, String)]
isDatatypeKeyAux iri = mapMaybe (\ (l, p) -> checkPredefAux l p iri)
  [ (xsdKeys, "xsd"), (owlNumbers, "owl"), ([xmlLiteral], "rdf")
  , ([rdfsLiteral], "rdfs")]

checkPredefAux :: [String] -> String -> IRI -> Maybe (String, String)
checkPredefAux sl pref u =
   let m1 = if elem (namePrefix u) ["", pref] then
              lookup (localPart u) $ map (\ a -> (a, (pref, a))) sl
            else Nothing
   in case m1 of
        Nothing -> lookup (showQU u) $ concatMap (\ a ->
           [ (Map.findWithDefault "" pref predefPrefixes ++ a, (pref, a))
           , (showQU dummyQName ++ "#" ++ a, (pref, a))]) sl
        _ -> m1

checkPredef :: [String] -> String -> IRI -> Bool
checkPredef sl pref = isJust . checkPredefAux sl pref

isOWLPredef :: [String] -> IRI -> Bool
isOWLPredef sl = checkPredef sl "owl"

-- | sets the correct prefix for the predefined datatypes
setDatatypePrefix :: IRI -> IRI
setDatatypePrefix iri = case isDatatypeKeyAux iri of
  (p, l) : _ -> setPrefix p $ mkQName l
  _ -> error $ showQU iri ++ " is not a predefined datatype"

-- | checks if the IRI is part of the built-in ones and puts the correct prefix
setReservedPrefix :: IRI -> IRI
setReservedPrefix iri
    | isDatatypeKey iri && null (namePrefix iri) = setDatatypePrefix iri
    | (isThing iri || isPredefDataProp iri || isPredefOWLAnnoProp iri
        || isPredefObjProp iri) && null (namePrefix iri) = setPrefix "owl" iri
    | isPredefRDFSAnnoProp iri = setPrefix "rdfs" iri
    | otherwise = iri

stripReservedPrefix :: IRI -> IRI
stripReservedPrefix = mkQName . getPredefName

{- | returns the name of the predefined IRI (e.g <xsd:string> returns "string"
    or <http://www.w3.org/2002/07/owl#real> returns "real") -}
getPredefName :: IRI -> String
getPredefName iri =
    if namePrefix iri `elem` ["", "xsd", "rdf", "rdfs", "owl"]
        then localPart iri
        else case mapMaybe (`stripPrefix` showQU iri)
                    $ Map.elems predefPrefixes of
                [s] -> s
                _ -> showQN iri

-- | Extracts Token from IRI
uriToTok :: IRI -> Token
uriToTok urI = mkSimpleId $ getPredefName urI

-- | Extracts Id from IRI
uriToId :: IRI -> Id
uriToId = simpleIdToId . uriToTok

-- | Extracts Id from Entities
entityToId :: Entity -> Id
entityToId = uriToId . cutIRI

printDatatype :: IRI -> String
printDatatype dt = showQU $
    if isDatatypeKey dt then stripReservedPrefix dt else dt

data DatatypeCat = OWL2Number | OWL2String | OWL2Bool | Other
    deriving (Show, Eq, Ord)

getDatatypeCat :: IRI -> DatatypeCat
getDatatypeCat iri = case isDatatypeKey iri of
    True
        | hasPrefXSD [booleanS] iri -> OWL2Bool
        | hasPrefXSD xsdNumbers iri || checkPredef owlNumbers "owl" iri
            -> OWL2Number
        | hasPrefXSD xsdStrings iri -> OWL2String
        | otherwise -> Other
    False -> Other

hasPrefXSD :: [String] -> IRI -> Bool
hasPrefXSD sl = checkPredef sl "xsd"

facetToIRI :: DatatypeFacet -> ConstrainingFacet
facetToIRI = setPrefix "xsd" . mkQName . showFacet

-- * Cardinalities

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

data Entity = Entity
  { entityKind :: EntityType
  , cutIRI :: IRI }
  deriving (Show, Eq, Ord)

instance GetRange Entity where
  getRange = iriPos . cutIRI
  rangeSpan = qNameRange . cutIRI

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

data Literal = Literal LexicalForm TypedOrUntyped | NumberLit FloatLit
    deriving (Show, Eq, Ord)

-- | non-negative integers given by the sequence of digits
data NNInt = NNInt [Int] deriving (Eq, Ord)

instance Show NNInt where
  show (NNInt l) = map intToDigit l

zeroNNInt :: NNInt
zeroNNInt = NNInt []

isZeroNNInt :: NNInt -> Bool
isZeroNNInt (NNInt l) = null l

data IntLit = IntLit
  { absInt :: NNInt
  , isNegInt :: Bool }
  deriving (Eq, Ord)

instance Show IntLit where
  show (IntLit n b) = (if b then ('-' :) else id) $ show n

zeroInt :: IntLit
zeroInt = IntLit zeroNNInt False

isZeroInt :: IntLit -> Bool
isZeroInt (IntLit n _) = isZeroNNInt n

negNNInt :: Bool -> NNInt -> IntLit
negNNInt b n = IntLit n b

negInt :: IntLit -> IntLit
negInt (IntLit n b) = IntLit n $ not b

data DecLit = DecLit
  { truncDec :: IntLit
  , fracDec :: NNInt }
  deriving (Eq, Ord)

instance Show DecLit where
  show (DecLit t f) = show t
    ++ if isZeroNNInt f then "" else
      '.' : show f

isDecInt :: DecLit -> Bool
isDecInt = isZeroNNInt . fracDec

negDec :: Bool -> DecLit -> DecLit
negDec b (DecLit t f) = DecLit (if b then negInt t else t) f

data FloatLit = FloatLit
  { floatBase :: DecLit
  , floatExp :: IntLit }
  deriving (Eq, Ord)

instance Show FloatLit where
  show (FloatLit b e) = show b
    ++ if isZeroInt e then "" else
      'E' : show e ++ "F"

isFloatDec :: FloatLit -> Bool
isFloatDec = isZeroInt . floatExp

isFloatInt :: FloatLit -> Bool
isFloatInt f = isFloatDec f && isDecInt (floatBase f)

floatToInt :: FloatLit -> IntLit
floatToInt = truncDec . floatBase

intToDec :: IntLit -> DecLit
intToDec i = DecLit i zeroNNInt

decToFloat :: DecLit -> FloatLit
decToFloat d = FloatLit d zeroInt

intToFloat :: IntLit -> FloatLit
intToFloat = decToFloat . intToDec

abInt :: IntLit -> IntLit
abInt int = int {isNegInt = False}

abDec :: DecLit -> DecLit
abDec dec = dec {truncDec = abInt $ truncDec dec}

abFloat :: FloatLit -> FloatLit
abFloat f = f {floatBase = abDec $ floatBase f}

isNegDec :: DecLit -> Bool
isNegDec d = isNegInt $ truncDec d

numberName :: FloatLit -> String
numberName f
    | isFloatInt f = integerS
    | isFloatDec f = decimalS
    | otherwise = floatS

cTypeS :: String
cTypeS = "^^"

-- * PROPERTY EXPRESSIONS

type InverseObjectProperty = ObjectPropertyExpression

data ObjectPropertyExpression = ObjectProp ObjectProperty
  | ObjectInverseOf InverseObjectProperty
        deriving (Show, Eq, Ord)

objPropToIRI :: ObjectPropertyExpression -> Individual
objPropToIRI opExp = case opExp of
    ObjectProp u -> u
    ObjectInverseOf objProp -> objPropToIRI objProp

type DataPropertyExpression = DataProperty

-- * DATA RANGES

data DataRange =
    DataType Datatype [(ConstrainingFacet, RestrictionValue)]
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

data AnnotationValue = AnnValue IRI | AnnValLit Literal
    deriving (Show, Eq, Ord)
