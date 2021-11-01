{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
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

import qualified Common.GlobalAnnotations as GA (PrefixMap)

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

changePrefixMapTypeToString :: GA.PrefixMap -> PrefixMap
changePrefixMapTypeToString = fmap show

changePrefixMapTypeToGA :: PrefixMap -> GA.PrefixMap
changePrefixMapTypeToGA = fmap (\s -> case parseIRICompoundCurie s of
    Just i -> i
    Nothing -> case parseIRI s of 
      Just i -> i
      Nothing -> error $ "Invalid IRI while OWL2.AS.changePrefixMapTypeToGA: "  ++ s
  )

predefPrefixesGA :: GA.PrefixMap
predefPrefixesGA = changePrefixMapTypeToGA $ Map.map (\v -> "<" ++ v ++ ">") predefPrefixes

predefPrefixes :: PrefixMap
predefPrefixes = Map.fromList
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#") ]

plainDatatypeIRI :: IRI
plainDatatypeIRI = IRI {
          iriScheme = "http:"
        , iriAuthority = Just $ IRIAuth "" "www.w3.org" ""
        , iriPath = stringToId "/1999/02/22-rdf-syntax-ns"
        , iriQuery = ""
        , iriFragment = "#PlainLiteral"
        , prefixName = "rdf"
        , isAbbrev = True
        , isBlankNode = False
        , hasAngles = False
        , iriPos = nullRange
        , iFragment = "PlainLiteral"
    }

type LexicalForm = String
type LanguageTag = String
type ImportIRI = IRI
type OntologyIRI = IRI
type VersionIRI = IRI
type Class = IRI
type Datatype = IRI
type ObjectProperty = IRI
type DataProperty = IRI
type DirectlyImportsDocuments = [IRI]
type AnnotationProperty = IRI
type Individual = IRI
type AnonymousIndividual = IRI
type NamedIndividual = IRI

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
rdfMap = preDefMaps [xmlLiteral, stringS, rdfPlainLiteralS] "rdf"

rdfsMap :: PreDefMaps
rdfsMap = preDefMaps [rdfsLiteral] "rdfs"

isDatatypeKeyAux :: IRI -> [(String, String)]
isDatatypeKeyAux i = mapMaybe (`checkPredefAux` i)
  [ xsdMap, owlNumbersMap, rdfMap, rdfsMap ]

-- (types, prefixname, prefix iri)
type PreDefMaps = ([String], String, String)

preDefMaps :: [String] -> String -> PreDefMaps
preDefMaps sl pref = let
  Just puri = Map.lookup pref predefPrefixes
 in (sl, pref, puri)

-- returns Maybe (prefix, keyword)
-- e.g. Just ("xsd", "string")
checkPredefAux :: PreDefMaps -> IRI -> Maybe (String, String)
checkPredefAux (sl, pref, exPref) u =
  let t = stripPrefix exPref (show $ u) in
    if isAbbrev u then
      if prefixName u == pref && iFragment u `elem` sl then
        Just (pref, iFragment u)
      else Nothing
    else case t of
      Just lp | lp `elem` sl -> Just (pref, lp)
      _ -> Nothing


checkPredef :: PreDefMaps -> IRI -> Bool
checkPredef ms = isJust . checkPredefAux ms

makeOWLPredefMaps :: [String] -> PreDefMaps
makeOWLPredefMaps sl = preDefMaps sl "owl"

-- | sets the correct prefix for the predefined datatypes
setDatatypePrefix :: IRI -> IRI
setDatatypePrefix i = case isDatatypeKeyAux i of
  (p, l) : _ -> i {prefixName = p, iFragment = l}
  _ -> error $ showIRICompact i ++ " is not a predefined datatype"

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
    if (isAbbrev i || (not (hasFullIRI i) && prefixName i `elem` ["", "xsd", "rdf", "rdfs", "owl"]))
    then stringToId $ iFragment i
    else stringToId $ case mapMaybe (`stripPrefix` showIRICompact i)
                $ Map.elems predefPrefixes of
            [s] -> s
            _ -> showIRIFull i
            
getPredefName :: IRI -> String
getPredefName = show . uriToId

-- | Extracts Token from IRI
uriToTok :: IRI -> Token
uriToTok = mkSimpleId . show . getPredefName

-- | Extracts Id from Entities
entityToId :: Entity -> Id
entityToId = uriToId . cutIRI

printDatatype :: IRI -> String
printDatatype dt = showIRICompact $
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
facetToIRI f = expandIRI predefPrefixesGA $ nullIRI {
    prefixName = "xsd"
  , iFragment = showFacet f
  , isAbbrev = True
}

facetToIRINoSign :: DatatypeFacet -> ConstrainingFacet
facetToIRINoSign f = expandIRI predefPrefixesGA $ nullIRI {
    prefixName = "xsd"
  , iFragment = showFacetAsText f
  , isAbbrev = True
}

-- * Extracting Symbols


-- symsOfAxiom :: Axiom -> Set.Set AS.Entity
-- symsOfAxiom (PlainAxiom e f) = Set.union (symsOfExtended e) $ symsOfFrameBit f

symsOfAxiom :: Axiom -> Set.Set Entity
symsOfAxiom ax = case ax of
    Declaration anns e -> Set.union (symsOfAnnotations anns) (Set.singleton e) 
    ClassAxiom cax -> case cax of
        SubClassOf anns supClExpr subClExpr -> Set.unions [
            (symsOfAnnotations anns),
            (symsOfClassExpression supClExpr),
            (symsOfClassExpression subClExpr)
          ]
        EquivalentClasses anns clExprs ->
          foldl Set.union (symsOfAnnotations anns)
            (map symsOfClassExpression clExprs) 
        DisjointClasses anns clExprs ->
          foldl Set.union (symsOfAnnotations anns)
            (map symsOfClassExpression clExprs) 
        DisjointUnion anns clIri clExprs ->
          foldl Set.union (Set.insert (mkEntity Class $ clIri) $ symsOfAnnotations anns)
            (map symsOfClassExpression clExprs)

    ObjectPropertyAxiom opax -> case opax of
        SubObjectPropertyOf anns subOpExpr supOpExpr ->
          let opExprs = case subOpExpr of
                SubObjPropExpr_obj opExpr -> [opExpr]
                SubObjPropExpr_exprchain opExprCh -> opExprCh
          in
            foldl Set.union (symsOfAnnotations anns)
              $ map symsOfObjectPropertyExpression . concat $ [opExprs, [supOpExpr]]
        EquivalentObjectProperties anns opExprs ->
          foldl Set.union (symsOfAnnotations anns)
            $ map symsOfObjectPropertyExpression opExprs
        DisjointObjectProperties anns opExprs -> 
          foldl Set.union (symsOfAnnotations anns) 
            $ map symsOfObjectPropertyExpression opExprs
        InverseObjectProperties anns opExpr1 opExpr2 ->
          foldl Set.union (symsOfAnnotations anns)
            $ map symsOfObjectPropertyExpression [opExpr1, opExpr2]
        ObjectPropertyDomain anns opExpr clExpr ->
          foldl Set.union (symsOfAnnotations anns)
            [ symsOfObjectPropertyExpression opExpr
            , symsOfClassExpression clExpr] 
        ObjectPropertyRange anns opExpr clExpr ->
          foldl Set.union (symsOfAnnotations anns)
            [ symsOfObjectPropertyExpression opExpr
            , symsOfClassExpression clExpr] 
        FunctionalObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr) 
        InverseFunctionalObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr) 
        ReflexiveObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr)  
        IrreflexiveObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr)  
        SymmetricObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr)  
        AsymmetricObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr)  
        TransitiveObjectProperty anns opExpr ->
          Set.union (symsOfAnnotations anns)
            (symsOfObjectPropertyExpression opExpr)  
    DataPropertyAxiom a -> case a of
        SubDataPropertyOf anns dpExpr1 dpExpr2 ->
          foldl Set.union (symsOfAnnotations anns)
            $ map (Set.singleton . mkEntity Datatype) [dpExpr1, dpExpr2] 
        EquivalentDataProperties anns dpExprs ->
          foldl Set.union (symsOfAnnotations anns)
            $ map (Set.singleton . mkEntity Datatype) dpExprs 
        DisjointDataProperties anns dpExprs ->
          foldl Set.union (symsOfAnnotations anns)
            $ map (Set.singleton . mkEntity Datatype) dpExprs
        DataPropertyDomain anns dpExpr clExpr ->
          foldl Set.union (symsOfAnnotations anns)
            [ Set.singleton . mkEntity Datatype $ dpExpr
            , symsOfClassExpression clExpr] 
        DataPropertyRange anns dpExpr dr ->
          foldl Set.union (symsOfAnnotations anns)
            [ Set.singleton . mkEntity Datatype $ dpExpr
            , symsOfDataRange dr] 
        FunctionalDataProperty anns dpExpr ->
          Set.union (symsOfAnnotations anns)
            (Set.singleton . mkEntity Datatype $ dpExpr)
    DatatypeDefinition anns dt dr ->
      foldl Set.union (symsOfAnnotations anns)
            [ Set.singleton . mkEntity Datatype $ dt
            , symsOfDataRange dr] 
    HasKey anns c os ds -> Set.unions [
        symsOfAnnotations anns,
        symsOfClassExpression c,
        Set.unions (symsOfObjectPropertyExpression <$> os),
        Set.fromList (mkEntity DataProperty <$> ds)
      ]
    Assertion a -> case a of
        SameIndividual anns inds -> Set.union
          (symsOfAnnotations anns)
          (Set.fromList (mkEntity NamedIndividual <$> inds))
        DifferentIndividuals anns inds -> Set.union
          (symsOfAnnotations anns)
          (Set.fromList (mkEntity NamedIndividual <$> inds))
        ClassAssertion anns _ i -> Set.insert (mkEntity NamedIndividual i) $
          Set.insert (mkEntity NamedIndividual i) (symsOfAnnotations anns)
        ObjectPropertyAssertion anns o s t -> Set.unions [
            symsOfAnnotations anns,
            symsOfObjectPropertyExpression o,
            Set.fromList (mkEntity NamedIndividual <$> [s, t])
          ]
        NegativeObjectPropertyAssertion anns o s t -> Set.unions [
            symsOfAnnotations anns,
            symsOfObjectPropertyExpression o,
            Set.fromList (mkEntity NamedIndividual <$> [s, t])
          ]
        DataPropertyAssertion anns d s _ -> Set.unions [
            symsOfAnnotations anns,
            Set.singleton $ mkEntity DataProperty d,
            Set.singleton $ mkEntity NamedIndividual s
          ]
        NegativeDataPropertyAssertion anns d s _ -> Set.unions [
            symsOfAnnotations anns,
            Set.singleton $ mkEntity DataProperty d,
            Set.singleton $ mkEntity NamedIndividual s
          ]
    AnnotationAxiom a -> case a of
        AnnotationAssertion anns p _ v -> symsOfAnnotation $ Annotation anns p v
        SubAnnotationPropertyOf anns p1 p2 -> Set.union
          (symsOfAnnotations anns)
          (Set.fromList (mkEntity AnnotationProperty <$> [p1, p2]))
        AnnotationPropertyDomain anns p _ -> Set.insert
          (mkEntity AnnotationProperty p)
          (symsOfAnnotations anns)
        AnnotationPropertyRange anns p _ -> Set.insert
          (mkEntity AnnotationProperty p)
          (symsOfAnnotations anns)
    Rule a -> case a of
      DLSafeRule anns b h -> Set.unions [
          symsOfAnnotations anns,
          symsOfDLSafeAtoms b,
          symsOfDLSafeAtoms h
        ]
      DGRule anns b h -> Set.unions [
          symsOfAnnotations anns,
          symsOfDGAtoms b,
          symsOfDGAtoms h
        ]
    DGAxiom _ _ _ e c -> Set.unions [
        symsOfDGEdges e,
        Set.fromList (mkEntity Class <$> c)
      ]

symsOfDGAtoms :: [DGAtom] -> Set.Set Entity
symsOfDGAtoms = Set.unions . fmap (\a -> case a of
    DGClassAtom e i -> Set.union (symsOfClassExpression e) (symsOfIArg i)
    DGObjectPropertyAtom o i1 i2 -> Set.unions [
        symsOfObjectPropertyExpression o,
        symsOfIArg i1,
        symsOfIArg i2
      ]
  )

symsOfDLSafeAtoms :: [Atom] -> Set.Set Entity
symsOfDLSafeAtoms = Set.unions . fmap (\a -> case a of
    ClassAtom e  i-> Set.union (symsOfClassExpression e) (symsOfIArg i)
    ObjectPropertyAtom o i1 i2 -> Set.unions [
        symsOfObjectPropertyExpression o,
        symsOfIArg i1,
        symsOfIArg i2
      ]
    DataPropertyAtom d i _ -> Set.insert (mkEntity DataProperty d) (symsOfIArg i)
    SameIndividualAtom i1 i2 -> Set.union (symsOfIArg i1) (symsOfIArg i2)
    DifferentIndividualsAtom i1 i2 -> Set.union (symsOfIArg i1) (symsOfIArg i2)
    _ -> mempty
  )

symsOfIArg :: IndividualArg -> Set.Set Entity
symsOfIArg a = case a of
  IArg i -> Set.singleton $ mkEntity NamedIndividual i
  _ -> mempty 

symsOfDGEdges :: DGEdges -> Set.Set Entity
symsOfDGEdges = Set.fromList . fmap (\(DGEdgeAssertion o _ _) ->
  mkEntity ObjectProperty o)

symsOfObjectPropertyExpression :: ObjectPropertyExpression -> Set.Set Entity
symsOfObjectPropertyExpression o = case o of
  ObjectProp i -> Set.singleton $ mkEntity ObjectProperty i
  ObjectInverseOf i -> symsOfObjectPropertyExpression i

symsOfClassExpression :: ClassExpression -> Set.Set Entity
symsOfClassExpression ce = case ce of
  Expression c -> Set.singleton $ mkEntity Class c
  ObjectJunction _ cs -> Set.unions $ map symsOfClassExpression cs
  ObjectComplementOf c -> symsOfClassExpression c
  ObjectOneOf is -> Set.fromList $ map (mkEntity NamedIndividual) is
  ObjectValuesFrom _ oe c -> Set.union (symsOfObjectPropertyExpression oe)
    $ symsOfClassExpression c
  ObjectHasValue oe i -> Set.insert (mkEntity NamedIndividual i)
    $ symsOfObjectPropertyExpression oe
  ObjectHasSelf oe -> symsOfObjectPropertyExpression oe
  ObjectCardinality (Cardinality _ _ oe mc) -> Set.union
    (symsOfObjectPropertyExpression oe)
    $ maybe Set.empty symsOfClassExpression mc
  DataValuesFrom _ de dr -> Set.union (Set.fromList $ map (mkEntity DataProperty) de)
    $ symsOfDataRange dr
  DataHasValue de _ -> Set.singleton $ mkEntity DataProperty de
  DataCardinality (Cardinality _ _ d m) -> Set.insert (mkEntity DataProperty d)
    $ maybe Set.empty symsOfDataRange m

symsOfDataRange :: DataRange -> Set.Set Entity
symsOfDataRange dr = case dr of
  DataType t _ -> Set.singleton $ mkEntity Datatype t
  DataJunction _ ds -> Set.unions $ map symsOfDataRange ds
  DataComplementOf d -> symsOfDataRange d
  DataOneOf _ -> Set.empty

symsOfAnnotation :: Annotation -> Set.Set Entity
symsOfAnnotation (Annotation as p _) = Set.insert
   (mkEntity AnnotationProperty p) $ Set.unions (map symsOfAnnotation as)

symsOfAnnotations :: [Annotation] -> Set.Set Entity
symsOfAnnotations = Set.unions . map symsOfAnnotation


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

isObjectProperty :: ObjectPropertyExpression -> Bool
isObjectProperty (ObjectProp _) = True
isObjectProperty _ = False

objPropToIRI :: ObjectPropertyExpression -> IRI
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
  | DataValuesFrom QuantifierType [DataPropertyExpression] DataRange
  | DataHasValue DataPropertyExpression Literal
  | DataCardinality (Cardinality DataPropertyExpression DataRange)
    deriving (Show, Eq, Ord, Typeable, Data)

-- * ANNOTATIONS

data Annotation = Annotation {
      annAnnotations :: [Annotation]
    , annProperty :: AnnotationProperty
    , annValue :: AnnotationValue
  }
    deriving (Show, Eq, Ord, Typeable, Data)

type OntologyAnnotations = [Annotation]


data AnnotationValue =
    AnnAnInd AnonymousIndividual
  | AnnValue IRI
  | AnnValLit Literal
    deriving (Show, Eq, Ord, Typeable, Data)

data AnnotationAxiom =
    AnnotationAssertion
      AxiomAnnotations
      AnnotationProperty
      AnnotationSubject
      AnnotationValue
  | SubAnnotationPropertyOf
    AxiomAnnotations
    SubAnnotationProperty
    SuperAnnotationProperty
  | AnnotationPropertyDomain AxiomAnnotations AnnotationProperty IRI
  | AnnotationPropertyRange AxiomAnnotations AnnotationProperty IRI
    deriving (Show, Eq, Ord, Data)

-- Annotation Assertion
data AnnotationSubject = AnnSubIri IRI | AnnSubAnInd AnonymousIndividual
    deriving (Show, Eq, Ord, Data)

-- Annotation Subproperties
type SubAnnotationProperty = AnnotationProperty
type SuperAnnotationProperty = AnnotationProperty


-- * AXIOMS

data Axiom =
  Declaration AxiomAnnotations Entity
  | ClassAxiom ClassAxiom
  | ObjectPropertyAxiom ObjectPropertyAxiom
  | DataPropertyAxiom DataPropertyAxiom
  | DatatypeDefinition AxiomAnnotations Datatype DataRange
  | HasKey
     AxiomAnnotations
     ClassExpression
     [ObjectPropertyExpression]
     [DataPropertyExpression]
  | Assertion Assertion
  | AnnotationAxiom AnnotationAxiom
  | Rule Rule
  | DGAxiom AxiomAnnotations DGName DGNodes DGEdges MainClasses
  deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange Axiom where
  getRange = Range . joinRanges . map rangeSpan . Set.toList . symsOfAxiom

-- ClassAxiom

type AxiomAnnotations = [Annotation]
type SubClassExpression = ClassExpression
type SuperClassExpression = ClassExpression

type DisjointClassExpression = [ClassExpression]
data ClassAxiom =
  SubClassOf AxiomAnnotations SubClassExpression SuperClassExpression
  | EquivalentClasses AxiomAnnotations [ClassExpression]
  | DisjointClasses AxiomAnnotations [ClassExpression]
  | DisjointUnion AxiomAnnotations Class DisjointClassExpression
  deriving (Show, Eq, Ord, Data)

-- ObjectAxiom

data ObjectPropertyAxiom =
  SubObjectPropertyOf
    AxiomAnnotations
    SubObjectPropertyExpression
    SuperObjectPropertyExpression
  | EquivalentObjectProperties AxiomAnnotations [ObjectPropertyExpression]
  | DisjointObjectProperties AxiomAnnotations [ObjectPropertyExpression]
  | InverseObjectProperties
      AxiomAnnotations
      ObjectPropertyExpression
      ObjectPropertyExpression
  | ObjectPropertyDomain
      AxiomAnnotations
      ObjectPropertyExpression
      ClassExpression
  | ObjectPropertyRange
      AxiomAnnotations
      ObjectPropertyExpression
      ClassExpression
  | FunctionalObjectProperty AxiomAnnotations ObjectPropertyExpression
  | InverseFunctionalObjectProperty AxiomAnnotations ObjectPropertyExpression
  | ReflexiveObjectProperty AxiomAnnotations ObjectPropertyExpression
  | IrreflexiveObjectProperty AxiomAnnotations ObjectPropertyExpression
  | SymmetricObjectProperty AxiomAnnotations ObjectPropertyExpression
  | AsymmetricObjectProperty AxiomAnnotations ObjectPropertyExpression
  | TransitiveObjectProperty AxiomAnnotations ObjectPropertyExpression
  deriving (Show, Eq, Ord, Data)

-- SubObjectPropertyOf

type PropertyExpressionChain = [ObjectPropertyExpression]
type SuperObjectPropertyExpression = ObjectPropertyExpression

data SubObjectPropertyExpression =
    SubObjPropExpr_obj ObjectPropertyExpression
  | SubObjPropExpr_exprchain PropertyExpressionChain
  deriving (Show, Eq, Ord, Data)

-- DataPropertyAxiom
data DataPropertyAxiom =
  SubDataPropertyOf AxiomAnnotations SubDataPropertyExpression
    SuperDataPropertyExpression
  | EquivalentDataProperties AxiomAnnotations [DataPropertyExpression]
      -- at least 2
  | DisjointDataProperties AxiomAnnotations [DataPropertyExpression]
    -- at least 2
  | DataPropertyDomain AxiomAnnotations DataPropertyExpression ClassExpression
  | DataPropertyRange AxiomAnnotations DataPropertyExpression DataRange
  | FunctionalDataProperty AxiomAnnotations DataPropertyExpression
  deriving (Show, Eq, Ord, Data)

type SubDataPropertyExpression = DataPropertyExpression
type SuperDataPropertyExpression = DataPropertyExpression


-- Assertions
data Assertion =
  SameIndividual AxiomAnnotations [Individual]
  | DifferentIndividuals AxiomAnnotations [Individual]
  | ClassAssertion AxiomAnnotations ClassExpression Individual
  | ObjectPropertyAssertion AxiomAnnotations ObjectPropertyExpression
    SourceIndividual TargetIndividual
  | NegativeObjectPropertyAssertion AxiomAnnotations ObjectPropertyExpression
    SourceIndividual TargetIndividual
  | DataPropertyAssertion AxiomAnnotations DataPropertyExpression
    SourceIndividual TargetValue
  | NegativeDataPropertyAssertion AxiomAnnotations DataPropertyExpression
    SourceIndividual TargetValue
  deriving (Show, Eq, Ord, Data)

type SourceIndividual = Individual
type TargetIndividual = Individual
type TargetValue = Literal

-- SWRL Rules

data Rule = DLSafeRule AxiomAnnotations Body Head
  | DGRule AxiomAnnotations DGBody DGHead
  deriving (Show, Eq, Ord, Data)
type Body = [Atom]
type Head = [Atom]
type DGBody = [DGAtom]
type DGHead = [DGAtom]

data IndividualArg = IArg Individual | IVar IndividualVar
  deriving (Show, Eq, Ord, Data)
data DataArg = DArg Literal | DVar DataVar
  deriving (Show, Eq, Ord, Data)

type IndividualVar = Variable
type DataVar = Variable
type Variable = IRI

-- | See `UnknownUnaryAtom`
data UnknownArg = IndividualArg IndividualArg | DataArg DataArg | Variable Variable
  deriving (Show, Eq, Ord, Data)

data Atom = ClassAtom ClassExpression IndividualArg
  | DataRangeAtom DataRange DataArg
  | ObjectPropertyAtom ObjectPropertyExpression IndividualArg IndividualArg
  | DataPropertyAtom DataProperty IndividualArg DataArg
  -- At least one DataArg
  | BuiltInAtom IRI [DataArg]
  | SameIndividualAtom IndividualArg IndividualArg
  | DifferentIndividualsAtom IndividualArg IndividualArg

{-|
  Ambiguous predicates used in SWRL Rules which type cannot be inferred during parsing
  This predicates get resolved and replaced with a specific one in static analysis.
-}
  | UnknownUnaryAtom IRI UnknownArg
  | UnknownBinaryAtom IRI UnknownArg UnknownArg
  deriving (Show, Eq, Ord, Data)


getVariablesFromIArg :: IndividualArg -> Set.Set Variable
getVariablesFromIArg iarg = case iarg of
    (IVar v) -> Set.singleton v
    _ -> mempty

getVariablesFromDArg :: DataArg -> Set.Set Variable
getVariablesFromDArg darg = case darg of
    (DVar v) -> Set.singleton v
    _ -> mempty

getVariablesFromAtom :: Atom -> Set.Set Variable
getVariablesFromAtom atom = case atom of
    ClassAtom _ (IVar var) -> Set.singleton var
    DataRangeAtom _ (DVar var) -> Set.singleton var
    ObjectPropertyAtom _ iarg1 iarg2 -> Set.unions $ getVariablesFromIArg <$> [iarg1, iarg2]
    DataPropertyAtom _ iarg darg -> getVariablesFromDArg darg `Set.union` getVariablesFromIArg iarg
    BuiltInAtom _ args -> Set.unions $ getVariablesFromDArg <$> args
    SameIndividualAtom iarg1 iarg2 -> Set.unions $ getVariablesFromIArg <$> [iarg1, iarg2]
    DifferentIndividualsAtom iarg1 iarg2 ->  Set.unions $ getVariablesFromIArg <$> [iarg1, iarg2]
    _ -> mempty

data DGAtom = DGClassAtom ClassExpression IndividualArg
  | DGObjectPropertyAtom ObjectPropertyExpression IndividualArg IndividualArg
  deriving (Show, Eq, Ord, Data)

type DGName = IRI
-- At least one
type DGNodes = [DGNodeAssertion]
-- At least one
type DGEdges = [DGEdgeAssertion]
-- At least one
type MainClasses = [Class]

data DGNodeAssertion = DGNodeAssertion Class DGNode
  deriving (Show, Eq, Ord, Data)
type DGNode = IRI

data DGEdgeAssertion = DGEdgeAssertion ObjectProperty DGNode DGNode
  deriving (Show, Eq, Ord, Data)

-- Root

emptyOntology :: Ontology
emptyOntology = Ontology Nothing Nothing [] [] []

emptyOntologyDoc :: OntologyDocument
emptyOntologyDoc = OntologyDocument (OntologyMetadata AS) mempty emptyOntology

data OntologySyntaxType = MS | AS | XML
  deriving  (Show, Eq, Ord, Data, Typeable)

data OntologyMetadata = OntologyMetadata {
  syntaxType :: OntologySyntaxType
  -- might be extended 
} deriving  (Show, Eq, Ord, Data, Typeable)

changeSyntax :: OntologySyntaxType -> OntologyDocument -> OntologyDocument
changeSyntax t o@(OntologyDocument m _ _) = o {
  ontologyMetadata = m {syntaxType = t}
}

data OntologyDocument = OntologyDocument {
    ontologyMetadata :: OntologyMetadata 
  , prefixDeclaration :: GA.PrefixMap
  , ontology :: Ontology
}
  deriving  (Show, Eq, Ord, Data, Typeable)

data PrefixDeclaration = PrefixDeclaration PrefixName IRI
  deriving  (Show, Eq, Ord, Data, Typeable)

instance GetRange OntologyDocument
  
type PrefixName = String

data Ontology = Ontology {
    mOntologyIRI :: (Maybe OntologyIRI)
  , mOntologyVersion :: (Maybe VersionIRI)
  , importsDocuments :: DirectlyImportsDocuments
  , ontologyAnnotation:: OntologyAnnotations
  , axioms :: [Axiom]
}
  deriving  (Show, Eq, Ord, Data)
