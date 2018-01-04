{- |
Module      :  ./OWL2/XML.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

OWL/XML Syntax Parsing
-}

module OWL2.XML
 ( xmlBasicSpec
 , splitIRI
 , isSmth
 ) where

import Common.Lexer (value)
import Common.IRI
import Common.Id (stringToId, prependString, tokStr, getTokens)

import OWL2.AS
import OWL2.Extract
import OWL2.Keywords
import OWL2.MS
import OWL2.XMLKeywords

import Text.XML.Light

import Data.Maybe
import Data.List
import qualified Data.Map as Map

import Debug.Trace

type XMLBase = String

-- | error messages for the parser
err :: String -> t
err s = error $ "XML parser: " ++ s

{- two functions from Text.XML.Light.Proc version 1.3.7 for compatibility
  with previous versions -}
vLookupAttrBy :: (Text.XML.Light.QName -> Bool) -> [Attr] -> Maybe String
vLookupAttrBy p as = attrVal `fmap` find (p . attrKey) as

vFindAttrBy :: (Text.XML.Light.QName -> Bool) -> Element -> Maybe String
vFindAttrBy p e = vLookupAttrBy p (elAttribs e)

isSmth :: String -> Text.XML.Light.QName -> Bool
isSmth s = (s ==) . qName

isSmthList :: [String] -> Text.XML.Light.QName -> Bool
isSmthList l qn = qName qn `elem` l

isNotSmth :: Text.XML.Light.QName -> Bool
isNotSmth q = let qn = qName q in qn `notElem` [declarationK,
    prefixK, importK, annotationK]

-- | parses all children with the given name
filterCh :: String -> Element -> [Element]
filterCh s = filterChildrenName (isSmth s)

-- | parses all children with names in the list
filterChL :: [String] -> Element -> [Element]
filterChL l = filterChildrenName (isSmthList l)

-- | parses one child with the given name
filterC :: String -> Element -> Element
filterC s e = fromMaybe (err "child not found")
    $ filterChildName (isSmth s) e

-- | parses one child with the name in the list
filterCL :: [String] -> Element -> Element
filterCL l e = fromMaybe (err "child not found")
    $ filterChildName (isSmthList l) e

-- | parses an IRI
getIRI :: XMLBase -> Element -> IRI
getIRI b e =
    let [a] = elAttribs e
        anIri = attrVal a
    in case qName $ attrKey a of
        "abbreviatedIRI" -> appendBase b $ nullIRI {iriPath = stringToId anIri, isAbbrev = True }
        "IRI" -> let x = parseIRIReference anIri -- todo: or combine parseIRI and parseIRIReference
                 in case x of
                     Just y -> appendBase b y
                     Nothing -> error $ "could not get IRI from " ++ show anIri
        "nodeID" -> appendBase b $ (mkIRI anIri){isBlankNode = True}
        _ -> error $ "wrong qName:" ++ show (attrKey a)
   

{- | if the IRI contains colon, it is split there;
else, the xml:base needs to be prepended to the local part
and then the IRI must be splitted -}
appendBase :: XMLBase -> IRI -> IRI
appendBase b iri =
    let r = iriPath iri
    in splitIRI $ if ':' `elem` show r
                   then iri
                   else iri {iriPath = prependString b r}

-- | splits an IRI at the colon
splitIRI :: IRI -> IRI
splitIRI iri = let 
  i = iriPath iri
  in if isBlankNode iri then mkNodeID iri else 
   case getTokens i of
    [] -> iri
    (tok:ts) ->
      let lp = tokStr tok
          (np, ':' : nlp) = span (/= ':') lp
      in iri { prefixName = np
            , iriPath = i { getTokens = tok { tokStr = nlp } : ts}
            }

-- | prepends "_:" to the nodeID if is not there already
mkNodeID :: IRI -> IRI
mkNodeID iri =
    let lp = show $ iriPath iri
    in case lp of
        '_' : ':' : r -> iri {prefixName = "_", iriPath = stringToId r}
        -- todo: maybe we should keep the Id structure of iriPath iri
        _ -> iri {prefixName = "_"}

-- | gets the content of an element with name Import
importIRI :: Map.Map String String -> XMLBase -> Element -> IRI
importIRI m b e =
  let cont1 = strContent e
      cont = Map.findWithDefault cont1 cont1 m
      anIri = nullIRI {iriPath = stringToId cont, isAbbrev = True}
  in appendBase b anIri

-- | gets the content of an element with name IRI, AbbreviatedIRI or Import
contentIRI :: XMLBase -> Element -> IRI
contentIRI b e =
  let cont = strContent e
      anIri = nullIRI {iriPath = stringToId cont, isAbbrev = True}
  in case getName e of
      "AbbreviatedIRI" -> splitIRI anIri
      "IRI" -> if ':' `elem` cont
                then splitIRI  anIri 
                else appendBase b anIri
      "Import" -> appendBase b $ anIri 
      _ -> err "invalid type of iri"

-- | gets the name of an axiom in XML Syntax
getName :: Element -> String
getName e =
  let u = elName e
      n = qName u
      q = qURI u
      p = qPrefix u
  in case q of
    Just "http://www.w3.org/2002/07/owl#" -> n
    _ -> if isNothing p then n else ""

-- | gets the cardinality
getInt :: Element -> Int
getInt e = let [int] = elAttribs e in value 10 $ attrVal int

getEntityType :: String -> EntityType
getEntityType ty = fromMaybe (err $ "no entity type " ++ ty)
  . lookup ty $ map (\ e -> (show e, e)) entityTypes

getEntity :: XMLBase -> Element -> Entity
getEntity b e = mkEntity (getEntityType $ (qName . elName) e) $ getIRI b e

getDeclaration :: XMLBase -> Element -> Axiom
getDeclaration b e = case getName e of
   "Declaration" ->
        PlainAxiom (mkExtendedEntity $ getEntity b $ filterCL entityList e)
            $ AnnFrameBit (getAllAnnos b e) $ AnnotationFrameBit Declaration
   _ -> err "not declaration"

isPlainLiteral :: String -> Bool
isPlainLiteral s =
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" == s

-- | put an "f" for float if not there already (eg. 123.45 --> 123.45f)
correctLit :: Literal -> Literal
correctLit l = case l of
    Literal lf (Typed dt) ->
        let nlf = if isSuffixOf "float" (show $ iriPath dt) && last lf /= 'f'
                then lf ++ "f"
                else lf
        in Literal nlf (Typed dt)
    _ -> l

getLiteral :: XMLBase -> Element -> Literal
getLiteral b e = case getName e of
    "Literal" ->
      let lf = strContent e
          mdt = findAttr (unqual "datatypeIRI") e
          mattr = vFindAttrBy (isSmth "lang") e
      in case mdt of
          Nothing -> case mattr of
             Just lang -> Literal lf $ Untyped $ Just lang
             Nothing -> Literal lf $ Untyped Nothing
          Just dt -> case mattr of
             Just lang -> Literal lf $ Untyped $ Just lang
             Nothing -> if isPlainLiteral dt then
                          Literal lf $ Untyped Nothing
                         else correctLit $ Literal lf $ Typed $ appendBase b $
                            nullIRI{iriPath = stringToId dt}
    _ -> err "not literal"

getValue :: XMLBase -> Element -> AnnotationValue
getValue b e = case getName e of
    "Literal" -> AnnValLit $ getLiteral b e
    "AnonymousIndividual" -> AnnValue $ getIRI b e
    _ -> AnnValue $ contentIRI b e

getSubject :: XMLBase -> Element -> IRI
getSubject b e = case getName e of
    "AnonymousIndividual" -> getIRI b e
    _ -> contentIRI b e

getAnnotation :: XMLBase -> Element -> Annotation
getAnnotation b e =
     let hd = filterCh "Annotation" e
         [ap] = filterCh "AnnotationProperty" e
         av = filterCL annotationValueList e
     in Annotation (map (getAnnotation b) hd) (getIRI b ap) $ getValue b av

-- | returns a list of annotations
getAllAnnos :: XMLBase -> Element -> [Annotation]
getAllAnnos b e = map (getAnnotation b) $ filterCh "Annotation" e

getObjProp :: XMLBase -> Element -> ObjectPropertyExpression
getObjProp b e = case getName e of
  "ObjectProperty" -> ObjectProp $ getIRI b e
  "ObjectInverseOf" ->
    let [ch] = elChildren e
        [cch] = elChildren ch
    in case getName ch of
      "ObjectInverseOf" -> getObjProp b cch
      "ObjectProperty" -> ObjectInverseOf $ ObjectProp $ getIRI b ch
      _ -> err "not objectProperty"
  _ -> err "not objectProperty"

-- | replaces eg. "minExclusive" with ">"
properFacet :: ConstrainingFacet -> ConstrainingFacet
properFacet cf
    | hasFullIRI cf =
        let p = showIRICompact cf \\ "http://www.w3.org/2001/XMLSchema#"
        in case p of
            "minInclusive" -> facetToIRI MININCLUSIVE
            "minExclusive" -> facetToIRI MINEXCLUSIVE
            "maxInclusive" -> facetToIRI MAXINCLUSIVE
            "maxExclusive" -> facetToIRI MAXEXCLUSIVE
            _ -> cf
    | otherwise = cf

getFacetValuePair :: XMLBase -> Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair b e = case getName e of
    "FacetRestriction" ->
       let [ch] = elChildren e
       in (properFacet $ getIRI b e, getLiteral b ch)
    _ -> err "not facet"

getDataRange :: XMLBase -> Element -> DataRange
getDataRange b e =
  let ch@(ch1 : _) = elChildren e
  in case getName e of
    "Datatype" -> DataType (getIRI b e) []
    "DatatypeRestriction" ->
        let dt = getIRI b $ filterC "Datatype" e
            fvp = map (getFacetValuePair b) $ filterCh "FacetRestriction" e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf $ getDataRange b ch1
    "DataOneOf" -> DataOneOf $ map (getLiteral b) $ filterCh "Literal" e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map (getDataRange b) ch
    "DataUnionOf" -> DataJunction UnionOf $ map (getDataRange b) ch
    _ -> err "not data range"

getClassExpression :: XMLBase -> Element -> ClassExpression
getClassExpression b e =
  let ch = elChildren e
      ch1 : _ = ch
      rch1 : _ = reverse ch
  in case getName e of
    "Class" -> Expression $ getIRI b e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map (getClassExpression b) ch
    "ObjectUnionOf" -> ObjectJunction UnionOf $ map (getClassExpression b) ch
    "ObjectComplementOf" -> ObjectComplementOf $ getClassExpression b ch1
    "ObjectOneOf" -> ObjectOneOf $ map (getIRI b) ch
    "ObjectSomeValuesFrom" -> ObjectValuesFrom SomeValuesFrom
            (getObjProp b ch1) $ getClassExpression b rch1
    "ObjectAllValuesFrom" -> ObjectValuesFrom AllValuesFrom
            (getObjProp b ch1) $ getClassExpression b rch1
    "ObjectHasValue" -> ObjectHasValue (getObjProp b ch1) $ getIRI b rch1
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp b ch1
    "DataSomeValuesFrom" -> DataValuesFrom SomeValuesFrom (getIRI b ch1)
            $ getDataRange b rch1
    "DataAllValuesFrom" -> DataValuesFrom AllValuesFrom (getIRI b ch1)
            $ getDataRange b rch1
    "DataHasValue" -> DataHasValue (getIRI b ch1) $ getLiteral b rch1
    _ -> getObjCard b e ch rch1

getObjCard :: XMLBase -> Element -> [Element] -> Element -> ClassExpression
getObjCard b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        op = getObjProp b ch1
        ce = if length ch == 2
                then Just $ getClassExpression b rch1
                else Nothing
    in case getName e of
        "ObjectMinCardinality" -> ObjectCardinality $ Cardinality
            MinCardinality i op ce
        "ObjectMaxCardinality" -> ObjectCardinality $ Cardinality
            MaxCardinality i op ce
        "ObjectExactCardinality" -> ObjectCardinality $ Cardinality
            ExactCardinality i op ce
        _ -> getDataCard b e ch rch1

getDataCard :: XMLBase -> Element -> [Element] -> Element -> ClassExpression
getDataCard b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        dp = getIRI b ch1
        dr = if length ch == 2
                then Just $ getDataRange b rch1
                else Nothing
    in case getName e of
        "DataMinCardinality" -> DataCardinality $ Cardinality
              MinCardinality i dp dr
        "DataMaxCardinality" -> DataCardinality $ Cardinality
              MaxCardinality i dp dr
        "DataExactCardinality" -> DataCardinality $ Cardinality
              ExactCardinality i dp dr
        _ -> err "not class expression"

getClassAxiom :: XMLBase -> Element -> Axiom
getClassAxiom b e =
   let ch = elChildren e
       as = getAllAnnos b e
       l@(hd : tl) = filterChL classExpressionList e
       [dhd, dtl] = filterChL dataRangeList e
       cel = map (getClassExpression b) l
   in case getName e of
    "SubClassOf" ->
       let [sub, super] = drop (length ch - 2) ch
       in PlainAxiom (ClassEntity $ getClassExpression b sub)
        $ ListFrameBit (Just SubClass) $ ExpressionBit
                      [(as, getClassExpression b super)]
    "EquivalentClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just $ EDRelation Equivalent) $ ExpressionBit $ emptyAnnoList cel
    "DisjointClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just $ EDRelation Disjoint) $ ExpressionBit $ emptyAnnoList cel
    "DisjointUnion" -> PlainAxiom (ClassEntity $ getClassExpression b hd)
        $ AnnFrameBit as $ ClassDisjointUnion $ map (getClassExpression b) tl
    "DatatypeDefinition" ->
        PlainAxiom (SimpleEntity $ mkEntity Datatype $ getIRI b dhd)
            $ AnnFrameBit as $ DatatypeBit $ getDataRange b dtl
    _ -> getKey b e

getKey :: XMLBase -> Element -> Axiom
getKey b e = case getName e of
  "HasKey" ->
    let as = getAllAnnos b e
        [ce] = filterChL classExpressionList e
        op = map (getObjProp b) $ filterChL objectPropList e
        dp = map (getIRI b) $ filterChL dataPropList e
    in PlainAxiom (ClassEntity $ getClassExpression b ce)
          $ AnnFrameBit as $ ClassHasKey op dp
  _ -> getOPAxiom b e

getOPAxiom :: XMLBase -> Element -> Axiom
getOPAxiom b e =
   let as = getAllAnnos b e
       op = getObjProp b $ filterCL objectPropList e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map $ getObjProp b) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let [o1, o2] = map (getObjProp b) $ filterChL objectPropList e
                  in PlainAxiom (ObjectEntity o1) $ ListFrameBit
                        (Just SubPropertyOf) $ ObjectBit [(as, o2)]
             else PlainAxiom (ObjectEntity op) $ AnnFrameBit as
                    $ ObjectSubPropertyChain opchain
    "EquivalentObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just $ EDRelation Equivalent)
            $ ObjectBit $ emptyAnnoList opl
    "DisjointObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just $ EDRelation Disjoint)
            $ ObjectBit $ emptyAnnoList opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
            (Just $ DRRelation ADomain) $ ExpressionBit [(as, ce)]
    "ObjectPropertyRange" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
            (Just $ DRRelation ARange) $ ExpressionBit [(as, ce)]
    "InverseObjectProperties" ->
       let [hd, lst] = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (ObjectEntity hd) $ ListFrameBit (Just InverseOf)
            $ ObjectBit [(as, lst)]
    "FunctionalObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Functional)]
    "InverseFunctionalObjectProperty" -> PlainAxiom (ObjectEntity op)
            $ ListFrameBit Nothing $ ObjectCharacteristics
            [(as, InverseFunctional)]
    "ReflexiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Reflexive)]
    "IrreflexiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Irreflexive)]
    "SymmetricObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Symmetric)]
    "AsymmetricObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Asymmetric)]
    "AntisymmetricObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Antisymmetric)]
    "TransitiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
            Nothing $ ObjectCharacteristics [(as, Transitive)]
    _ -> getDPAxiom b e

getDPAxiom :: XMLBase -> Element -> Axiom
getDPAxiom b e =
   let as = getAllAnnos b e
   in case getName e of
    "SubDataPropertyOf" ->
        let [hd, lst] = map (getIRI b) $ filterChL dataPropList e
        in PlainAxiom (SimpleEntity $ mkEntity DataProperty hd)
              $ ListFrameBit (Just SubPropertyOf) $ DataBit [(as, lst)]
    "EquivalentDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just $ EDRelation Equivalent)
            $ DataBit $ emptyAnnoList dpl
    "DisjointDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just $ EDRelation Disjoint)
            $ DataBit $ emptyAnnoList dpl
    "DataPropertyDomain" ->
        let dp = getIRI b $ filterCL dataPropList e
            ce = getClassExpression b $ filterCL classExpressionList e
        in PlainAxiom (SimpleEntity $ mkEntity DataProperty dp) $ ListFrameBit
                (Just $ DRRelation ADomain) $ ExpressionBit [(as, ce)]
    "DataPropertyRange" ->
        let dp = getIRI b $ filterCL dataPropList e
            dr = getDataRange b $ filterCL dataRangeList e
        in PlainAxiom (SimpleEntity $ mkEntity DataProperty dp)
                $ ListFrameBit Nothing $ DataPropRange [(as, dr)]
    "FunctionalDataProperty" ->
        let dp = getIRI b $ filterCL dataPropList e
        in PlainAxiom (SimpleEntity $ mkEntity DataProperty dp)
                $ AnnFrameBit as DataFunctional
    _ -> getDataAssertion b e

getDataAssertion :: XMLBase -> Element -> Axiom
getDataAssertion b e =
   let as = getAllAnnos b e
       dp = getIRI b $ filterCL dataPropList e
       ind = getIRI b $ filterCL individualList e
       lit = getLiteral b $ filterC "Literal" e
   in case getName e of
    "DataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ mkEntity NamedIndividual ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, DataPropertyFact Positive dp lit)]
    "NegativeDataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ mkEntity NamedIndividual ind)
            $ ListFrameBit Nothing $ IndividualFacts
               [(as, DataPropertyFact Negative dp lit)]
    _ -> getObjectAssertion b e

getObjectAssertion :: XMLBase -> Element -> Axiom
getObjectAssertion b e =
   let as = getAllAnnos b e
       op = getObjProp b $ filterCL objectPropList e
       [hd, lst] = map (getIRI b) $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ mkEntity NamedIndividual hd)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Positive op lst)]
    "NegativeObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ mkEntity NamedIndividual hd)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Negative op lst)]
    _ -> getIndividualAssertion b e

getIndividualAssertion :: XMLBase -> Element -> Axiom
getIndividualAssertion b e =
   let as = getAllAnnos b e
       ind = map (getIRI b) $ filterChL individualList e
       l = emptyAnnoList ind
   in case getName e of
    "SameIndividual" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Same))
          $ IndividualSameOrDifferent l
    "DifferentIndividuals" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Different))
          $ IndividualSameOrDifferent l
    _ -> getClassAssertion b e

getClassAssertion :: XMLBase -> Element -> Axiom
getClassAssertion b e = case getName e of
    "ClassAssertion" ->
        let as = getAllAnnos b e
            ce = getClassExpression b $ filterCL classExpressionList e
            ind = getIRI b $ filterCL individualList e
        in PlainAxiom (SimpleEntity $ mkEntity NamedIndividual ind)
                $ ListFrameBit (Just Types) $ ExpressionBit [(as, ce)]
    _ -> getAnnoAxiom b e

getAnnoAxiom :: XMLBase -> Element -> Axiom
getAnnoAxiom b e =
   let as = getAllAnnos b e
       ap = getIRI b $ filterC "AnnotationProperty" e
       [ch] = filterChL [iriK, abbreviatedIRI] e
       anIri = contentIRI b ch
    in case getName e of
    "AnnotationAssertion" ->
       let [s, v] = filterChL annotationValueList e
           sub = getSubject b s
       -- the misc will be converted to entities in static analysis
       in PlainAxiom (Misc [Annotation [] sub $ AnnValue sub])
           $ AnnFrameBit [Annotation as ap (getValue b v)]
                    $ AnnotationFrameBit Assertion
    "SubAnnotationPropertyOf" ->
        let [hd, lst] = map (getIRI b) $ filterCh "AnnotationProperty" e
        in PlainAxiom (SimpleEntity $ mkEntity AnnotationProperty hd)
            $ ListFrameBit (Just SubPropertyOf) $ AnnotationBit [(as, lst)]
    "AnnotationPropertyDomain" ->
        PlainAxiom (SimpleEntity $ mkEntity AnnotationProperty ap)
               $ ListFrameBit (Just $ DRRelation ADomain)
                      $ AnnotationBit [(as, anIri)]
    "AnnotationPropertyRange" ->
        PlainAxiom (SimpleEntity $ mkEntity AnnotationProperty ap)
               $ ListFrameBit (Just $ DRRelation ARange)
                      $ AnnotationBit [(as, anIri)]
    _ -> PlainAxiom (Misc []) . AnnFrameBit [] . AnnotationFrameBit
      . XmlError $ getName e

xmlErrorString :: Axiom -> Maybe String
xmlErrorString a = case a of
   PlainAxiom (Misc []) (AnnFrameBit [] (AnnotationFrameBit (XmlError e)))
     -> Just e
   _ -> Nothing

getFrames :: XMLBase -> Element -> [Axiom] -> [Frame]
getFrames b e ax =
   let f = map (axToFrame . getDeclaration b) (filterCh "Declaration" e)
           ++ map axToFrame (filter (isNothing . xmlErrorString) ax)
   in f ++ signToFrames f

getOnlyAxioms :: XMLBase -> Element -> [Axiom]
getOnlyAxioms b e = map (getClassAxiom b) $ filterChildrenName isNotSmth e

getImports :: Map.Map String String -> XMLBase -> Element -> [ImportIRI]
getImports m b e = map (importIRI m b) $ filterCh importK e

get1Map :: Element -> (String, String)
get1Map e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, pmap)

getPrefixMap :: Element -> [(String, String)]
getPrefixMap e = map get1Map $ filterCh "Prefix" e

getOntologyIRI :: XMLBase -> Element -> OntologyIRI
getOntologyIRI b e =
  let oi = findAttr (unqual "ontologyIRI") e
  in case oi of
    Nothing -> dummyIRI
    Just anIri -> appendBase b
        $ nullIRI {iriPath = stringToId anIri, isAbbrev = True}

getBase :: Element -> XMLBase
getBase e = fromJust $ vFindAttrBy (isSmth "base") e

-- | parses an ontology document
xmlBasicSpec :: Map.Map String String -> Element -> OntologyDocument
xmlBasicSpec imap e =
    let b = getBase e
        ax = getOnlyAxioms b e
        es = mapMaybe xmlErrorString ax
        em = Map.fromListWith (+) $ map (\ s -> (s, 1 :: Int)) es
    in
    (if Map.null em then id else
      trace ("ignored element tags: "
             ++ unwords (map (\ (s, c) ->
                if c > 1 then s ++ " (" ++ show c ++ " times)" else s)
                         $ Map.toList em)))
    $ OntologyDocument (Map.fromList $ getPrefixMap e)
    (emptyOntology $ getFrames b e ax)
        {
        imports = getImports imap b e,
        ann = [getAllAnnos b e],
        name = getOntologyIRI b e
        }
