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
import Common.SetColimit
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


{-
data IRIType = Full | Abbreviated | NodeID
    deriving (Show, Eq, Ord, Typeable, Data)

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
  } deriving (Show, Typeable, Data)

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

-- | show QName in angle brackets as full iris
showQI :: QName -> String
showQI n = '<' : showQU n ++ ">"

nullQName :: QName
nullQName = QN "" "" Abbreviated "" nullRange


isNullQName :: QName -> Bool
isNullQName qn = case qn of
    QN "" "" _ "" _ -> True
    _ -> False

unamedS :: String
unamedS = "//www." ++ dnamedS

dnamedS :: String
dnamedS = "hets.eu/ontology/unamed"

dummyQName :: QName
dummyQName = QN "http" unamedS Full ("http:" ++ unamedS) nullRange

mkIRI :: String -> QName
mkIRI s = nullQName { localPart = s }

setQRange :: Range -> QName -> QName
setQRange r q = q { iriPos = r }

setPrefix :: String -> QName -> QName
setPrefix s q = q { namePrefix = s }

setFull :: QName -> QName
setFull q = q {iriType = Full}

type IRI = QName

instance SymbolName QName where
 addString (q, s) = q { localPart = localPart q ++ s,
                             expandedIRI = expandedIRI q ++ s
                           }


-- | checks if an IRI is an anonymous individual
isAnonymous :: IRI -> Bool
isAnonymous iri = iriType iri == NodeID || namePrefix iri == "_"

-- | checks if a string (bound to be localPart of an IRI) contains \":\/\/\"
cssIRI :: String -> IRIType
cssIRI iri = if isInfixOf "://" iri then Full else Abbreviated
-}

-- | checks if an IRI is an anonymous individual
isAnonymous :: IRI -> Bool
isAnonymous iri = prefixName iri == "_" 
 -- TODO: was also checking that the type is NodeID, but we don't have that now! 


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
    SubPropertyOf -> "subPropertyOfC"
    InverseOf -> "inverseOfC"
    SubClass -> "subClassOfC"
    Types -> "typesC"
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
    AllValuesFrom -> "onlyS"
    SomeValuesFrom -> "someS"

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
isPredefAnnoProp iri = isPredefOWLAnnoProp iri || isPredefRDFSAnnoProp iri

isPredefPropOrClass :: IRI -> Bool
isPredefPropOrClass iri = isPredefAnnoProp iri || isPredefDataProp iri
    || isPredefObjProp iri || isThing iri

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
isDatatypeKeyAux iri = mapMaybe (`checkPredefAux` iri)
  [ xsdMap, owlNumbersMap, rdfMap, rdfsMap ]

type PreDefMaps = ([String], String, String)

preDefMaps :: [String] -> String -> PreDefMaps
preDefMaps sl pref = let
  Just puri = Map.lookup pref predefPrefixes
  Just sp = stripPrefix "http://www.w3.org/" puri
 in (sl, pref, sp)

checkPredefAux :: PreDefMaps -> IRI -> Maybe (String, String)
checkPredefAux (sl, pref, exPref) u = Nothing
{-
  let lp = localPart u
      nn = dnamedS ++ "#"
      res = Just (pref, lp)
  in case namePrefix u of
    "http" -> case stripPrefix "//www." lp of
        Just q -> case stripPrefix "w3.org/" q of
            Just r -> case stripPrefix exPref r of
              Just s | elem s sl -> Just (pref, s)
              _ -> Nothing
            Nothing -> case stripPrefix nn q of
              Just s | elem s sl -> Just (pref, s)
              _ -> Nothing
        Nothing -> Nothing
    pu | elem lp sl -> case pu of
      "" -> let ex = expandedIRI u in
            case stripPrefix "http://www." ex of
              Just r | r == "w3.org/" ++ exPref ++ lp || r == nn ++ lp
                  -> res
              _ | null ex -> res
              _ -> Nothing
      _ | pu == pref -> Just (pref, lp)
      _ -> Nothing
    _ -> Nothing
-}

checkPredef :: PreDefMaps -> IRI -> Bool
checkPredef ms = isJust . checkPredefAux ms

makeOWLPredefMaps :: [String] -> PreDefMaps
makeOWLPredefMaps sl = preDefMaps sl "owl"

-- | sets the correct prefix for the predefined datatypes
setDatatypePrefix :: IRI -> IRI
setDatatypePrefix iri = case isDatatypeKeyAux iri of
  (p, l) : _ -> setPrefix p $ mkIRI l
  _ -> error $ showIRIU iri ++ " is not a predefined datatype"

-- | checks if the IRI is part of the built-in ones and puts the correct prefix
setReservedPrefix :: IRI -> IRI
setReservedPrefix iri = case prefixName iri of
  ""
    | isDatatypeKey iri -> setDatatypePrefix iri
    | isThing iri || isPredefDataProp iri || isPredefOWLAnnoProp iri
        || isPredefObjProp iri -> setPrefix "owl" iri
    | isPredefRDFSAnnoProp iri -> setPrefix "rdfs" iri
  _ -> iri

stripReservedPrefix :: IRI -> IRI
stripReservedPrefix = mkIRI . getPredefName

{- | returns the name of the predefined IRI (e.g <xsd:string> returns "string"
    or <http://www.w3.org/2002/07/owl#real> returns "real") -}
getPredefName :: IRI -> String
getPredefName iri =
    if prefixName iri `elem` ["", "xsd", "rdf", "rdfs", "owl"]
        then abbrevPath iri
        else case mapMaybe (`stripPrefix` showIRIU iri)
                    $ Map.elems predefPrefixes of
                [s] -> s
                _ -> showIRII iri

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
printDatatype dt = showIRIU $
    if isDatatypeKey dt then stripReservedPrefix dt else dt

data DatatypeCat = OWL2Number | OWL2String | OWL2Bool | Other
    deriving (Show, Eq, Ord, Typeable, Data)

getDatatypeCat :: IRI -> DatatypeCat
getDatatypeCat iri = case isDatatypeKey iri of
    True
        | checkPredef xsdBooleanMap iri -> OWL2Bool
        | checkPredef xsdNumbersMap iri || checkPredef owlNumbersMap iri
            -> OWL2Number
        | checkPredef xsdStringsMap iri -> OWL2String
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
        pairIRIs i1 i2 = nullIRI
          { prefixName = prefixName i1
          , abbrevPath = if rest (abbrevPath i1) == 
                            rest (abbrevPath i2) 
                          then abbrevPath i1 
                          else (abbrevPath i1) ++ "_" ++ (abbrevPath i2)
          } -- TODO: made it compile, but most likely will cause issues!
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
