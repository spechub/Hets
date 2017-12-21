{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/AS.hs
Copyright   :  (c) C. Maeder, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexander.Koslowski@st.ovgu.de
Stability   :  provisional
Portability :  portable

OWL 2 Functional Syntax constructs

References:
 <http://www.w3.org/TR/2009/REC-owl2-syntax-20091027/#Functional-Style_Syntax>
 <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.AS where

import Common.Id
import Common.Keywords (stringS)
import Common.IRI

import Common.Result

import OWL2.ColonKeywords
import OWL2.Keywords

import Data.Char (intToDigit)
import Data.Data
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | checks if an IRI is an anonymous individual
isAnonymous :: IRI -> Bool
isAnonymous i = prefixName i == "_" && isBlankNode i

-- | prefix -> localname
type PrefixMap = Map.Map String String

predefPrefixes :: PrefixMap
predefPrefixes = Map.fromList
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
      , ("", showIRIU dummyIRI ++ "#") ]

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
    deriving (Show, Eq, Ord, Typeable, Data)

showEquivOrDisjoint :: EquivOrDisjoint -> String
showEquivOrDisjoint ed = case ed of
    Equivalent -> equivalentToC
    Disjoint -> disjointWithC

data DomainOrRange = ADomain | ARange
    deriving (Show, Eq, Ord, Typeable, Data)

showDomainOrRange :: DomainOrRange -> String
showDomainOrRange dr = case dr of
    ADomain -> domainC
    ARange -> rangeC

data SameOrDifferent = Same | Different
    deriving (Show, Eq, Ord, Typeable, Data)

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
    deriving (Show, Eq, Ord, Typeable, Data)

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
    deriving (Enum, Bounded, Show, Eq, Ord, Typeable, Data)

data PositiveOrNegative = Positive | Negative
    deriving (Show, Eq, Ord, Typeable, Data)

data QuantifierType = AllValuesFrom | SomeValuesFrom
    deriving (Show, Eq, Ord, Typeable, Data)

showQuantifierType :: QuantifierType -> String
showQuantifierType ty = case ty of
    AllValuesFrom -> onlyS
    SomeValuesFrom -> someS

-- * Predefined IRI checkings

thingMap :: PreDefMaps
thingMap = makeOWLPredefMaps predefClass

isThing :: IRI -> Bool
isThing = checkPredef thingMap

makePredefObjProp :: PreDefMaps
makePredefObjProp = makeOWLPredefMaps predefObjProp

isPredefObjProp :: IRI -> Bool
isPredefObjProp = checkPredef makePredefObjProp

makePredefDataProp :: PreDefMaps
makePredefDataProp = makeOWLPredefMaps predefDataProp

isPredefDataProp :: IRI -> Bool
isPredefDataProp = checkPredef makePredefDataProp

makePredefRDFSAnnoProp :: PreDefMaps
makePredefRDFSAnnoProp = preDefMaps predefRDFSAnnoProps "rdfs"

isPredefRDFSAnnoProp :: IRI -> Bool
isPredefRDFSAnnoProp = checkPredef makePredefRDFSAnnoProp

makePredefOWLAnnoProp :: PreDefMaps
makePredefOWLAnnoProp = makeOWLPredefMaps predefOWLAnnoProps

isPredefOWLAnnoProp :: IRI -> Bool
isPredefOWLAnnoProp = checkPredef makePredefOWLAnnoProp

isPredefAnnoProp :: IRI -> Bool
isPredefAnnoProp i = isPredefOWLAnnoProp i || isPredefRDFSAnnoProp i

isPredefPropOrClass :: IRI -> Bool
isPredefPropOrClass i = isPredefAnnoProp i || isPredefDataProp i
    || isPredefObjProp i || isThing i

predefIRIs :: Set.Set IRI
predefIRIs = Set.fromList $ map (setPrefix "xsd" . mkIRI) xsdKeys
    ++ map (setPrefix "owl" . mkIRI) owlNumbers
    ++ map (setPrefix "rdf" . mkIRI) [rdfsLiteral, stringS]
    ++ [setPrefix "rdfs" $ mkIRI xmlLiteral]

isDatatypeKey :: IRI -> Bool
isDatatypeKey = not . null . isDatatypeKeyAux

xsdMap :: PreDefMaps
xsdMap = makeXsdMap xsdKeys

owlNumbersMap :: PreDefMaps
owlNumbersMap = makeOWLPredefMaps owlNumbers

rdfMap :: PreDefMaps
rdfMap = preDefMaps [xmlLiteral, stringS] "rdf"

rdfsMap :: PreDefMaps
rdfsMap = preDefMaps [rdfsLiteral] "rdfs"

isDatatypeKeyAux :: IRI -> [(String, String)]
isDatatypeKeyAux i = mapMaybe (`checkPredefAux` i)
  [ xsdMap, owlNumbersMap, rdfMap, rdfsMap ]

type PreDefMaps = ([String], String, String)

preDefMaps :: [String] -> String -> PreDefMaps
preDefMaps sl pref = let
  Just puri = Map.lookup pref predefPrefixes
  Just sp = stripPrefix "http://www.w3.org/" puri
 in (sl, pref, sp)

checkPredefAux :: PreDefMaps -> IRI -> Maybe (String, String)
checkPredefAux (sl, pref, exPref) u =
  let lp = show $ iriPath u
      res = Just (pref, lp)
  in case prefixName u of
    "http" -> case stripPrefix "//www." lp of
        Just q -> case stripPrefix "w3.org/" q of
            Just r -> case stripPrefix exPref r of
              Just s | elem s sl -> Just (pref, s)
              _ -> Nothing
            Nothing -> Nothing
        Nothing -> Nothing
    pu | elem lp sl -> case pu of
      "" -> let ex = iriToStringUnsecure u in 
            case stripPrefix "http://www." ex of
              Just r | r == "w3.org/" ++ exPref ++ lp -- || r == lp
                  -> res
              _ | null ex -> res
              _ -> Nothing
      _ | pref == pu || pref ++ ":" == pu -> Just (pref, lp)
      _ -> Nothing
    _ -> Nothing


checkPredef :: PreDefMaps -> IRI -> Bool
checkPredef ms = isJust . checkPredefAux ms

makeOWLPredefMaps :: [String] -> PreDefMaps
makeOWLPredefMaps sl = preDefMaps sl "owl"

-- | sets the correct prefix for the predefined datatypes
setDatatypePrefix :: IRI -> IRI
setDatatypePrefix i = case isDatatypeKeyAux i of
  (p, l) : _ -> setPrefix p $ mkIRI l
  _ -> error $ showIRIU i ++ " is not a predefined datatype"

-- | checks if the IRI is part of the built-in ones and puts the correct prefix
setReservedPrefix :: IRI -> IRI
setReservedPrefix i = case prefixName i of
  ""
    | isDatatypeKey i -> setDatatypePrefix i
    | isThing i || isPredefDataProp i || isPredefOWLAnnoProp i
        || isPredefObjProp i -> setPrefix "owl" i
    | isPredefRDFSAnnoProp i -> setPrefix "rdfs" i
  _ -> i

stripReservedPrefix :: IRI -> IRI
stripReservedPrefix = idToIRI . uriToId

{- | Extracts Id from IRI
     returns the name of the predefined IRI (e.g <xsd:string> returns "string"
     or <http://www.w3.org/2002/07/owl#real> returns "real") -}
uriToId :: IRI -> Id
uriToId i =
    if (prefixName i `elem` ["", "xsd", "rdf", "rdfs", "owl"])
       || (   null (iriScheme i)
           && null (iriQuery i)
           && null (iriFragment i)
           && isNothing (iriAuthority i))
        then iriPath i
        else stringToId $ case mapMaybe (`stripPrefix` showIRIU i)
                    $ Map.elems predefPrefixes of
                [s] -> s
                _ -> showIRII i

getPredefName :: IRI -> String
getPredefName = show . uriToId

-- | Extracts Token from IRI
uriToTok :: IRI -> Token
uriToTok = mkSimpleId . show . getPredefName

-- | Extracts Id from Entities
entityToId :: Entity -> Id
entityToId = uriToId . cutIRI

printDatatype :: IRI -> String
printDatatype dt = showIRIU $
    if isDatatypeKey dt then stripReservedPrefix dt else dt

data DatatypeCat = OWL2Number | OWL2String | OWL2Bool | Other
    deriving (Show, Eq, Ord, Typeable, Data)

getDatatypeCat :: IRI -> DatatypeCat
getDatatypeCat i = case isDatatypeKey i of
    True
        | checkPredef xsdBooleanMap i -> OWL2Bool
        | checkPredef xsdNumbersMap i || checkPredef owlNumbersMap i
            -> OWL2Number
        | checkPredef xsdStringsMap i -> OWL2String
        | otherwise -> Other
    False -> Other

makeXsdMap :: [String] -> PreDefMaps
makeXsdMap sl = preDefMaps sl "xsd"

xsdBooleanMap :: PreDefMaps
xsdBooleanMap = makeXsdMap [booleanS]

xsdNumbersMap :: PreDefMaps
xsdNumbersMap = makeXsdMap xsdNumbers

xsdStringsMap :: PreDefMaps
xsdStringsMap = makeXsdMap xsdStrings

facetToIRI :: DatatypeFacet -> ConstrainingFacet
facetToIRI = setPrefix "xsd" . mkIRI . showFacet

-- * Cardinalities

data CardinalityType = MinCardinality | MaxCardinality | ExactCardinality
    deriving (Show, Eq, Ord, Typeable, Data)

showCardinalityType :: CardinalityType -> String
showCardinalityType ty = case ty of
    MinCardinality -> minS
    MaxCardinality -> maxS
    ExactCardinality -> exactlyS

data Cardinality a b = Cardinality CardinalityType Int a (Maybe b)
    deriving (Show, Eq, Ord, Typeable, Data)

data JunctionType = UnionOf | IntersectionOf
    deriving (Show, Eq, Ord, Typeable, Data)

type ConstrainingFacet = IRI
type RestrictionValue = Literal

-- * ENTITIES

data Entity = Entity
  { label :: Maybe String
  , entityKind :: EntityType
  , cutIRI :: IRI }
  deriving (Show, Typeable, Data)

mkEntity :: EntityType -> IRI -> Entity
mkEntity = Entity Nothing

mkEntityLbl :: String -> EntityType -> IRI -> Entity
mkEntityLbl = Entity . Just

instance Ord Entity where
  compare (Entity _ ek1 ir1) (Entity _ ek2 ir2) = compare (ek1, ir1) (ek2, ir2)

instance Eq Entity where
  e1 == e2 = compare e1 e2 == EQ

instance GetRange Entity where
  getRange = iriPos . cutIRI
  rangeSpan = iRIRange . cutIRI

data EntityType =
    Datatype
  | Class
  | ObjectProperty
  | DataProperty
  | AnnotationProperty
  | NamedIndividual
    deriving (Enum, Bounded, Show, Read, Eq, Ord, Typeable, Data)

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

pairSymbols :: Entity -> Entity -> Result Entity -- TODO: improve!
pairSymbols (Entity lb1 k1 i1) (Entity lb2 k2 i2) =
  if k1 /= k2 then
    error "can't pair symbols of different kind"
   else do
    let rest x = drop 1 $ dropWhile (/= '#') x
        pairLables lbl1 lbl2 = case (lbl1, lbl2) of
            (Nothing, _) -> pairLables lbl2 lbl1
            (Just l1, Just l2) | l1 /= l2 -> Just $ l1 ++ ", " ++ l2
            _ -> lbl1
        pairIRIs iri1 iri2 = nullIRI
          { prefixName = prefixName iri1
          , iriPath = if rest (show $ iriPath iri1) == 
                            rest (show $ iriPath iri2) 
                          then iriPath iri1 
                          else appendId (iriPath iri1) (iriPath iri2)
          } -- TODO: improve, see #1597 
    return $ Entity (pairLables lb1 lb2) k1 $ pairIRIs i1 i2

-- * LITERALS

data TypedOrUntyped = Typed Datatype | Untyped (Maybe LanguageTag)
    deriving (Show, Eq, Ord, Typeable, Data)

data Literal = Literal LexicalForm TypedOrUntyped | NumberLit FloatLit
    deriving (Show, Eq, Ord, Typeable, Data)

-- | non-negative integers given by the sequence of digits
data NNInt = NNInt [Int] deriving (Eq, Ord, Typeable, Data)

instance Show NNInt where
  show (NNInt l) = map intToDigit l

zeroNNInt :: NNInt
zeroNNInt = NNInt []

isZeroNNInt :: NNInt -> Bool
isZeroNNInt (NNInt l) = null l

data IntLit = IntLit
  { absInt :: NNInt
  , isNegInt :: Bool }
  deriving (Eq, Ord, Typeable, Data)

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
  deriving (Eq, Ord, Typeable, Data)

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
  deriving (Eq, Ord, Typeable, Data)

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
        deriving (Show, Eq, Ord, Typeable, Data)

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
    deriving (Show, Eq, Ord, Typeable, Data)

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
    deriving (Show, Eq, Ord, Typeable, Data)

-- * ANNOTATIONS

data Annotation = Annotation [Annotation] AnnotationProperty AnnotationValue
    deriving (Show, Eq, Ord, Typeable, Data)

data AnnotationValue = AnnValue IRI | AnnValLit Literal
    deriving (Show, Eq, Ord, Typeable, Data)
