{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 XML Syntax Parsing
-}

module OWL2.XML where

import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS
import OWL2.Extract
import OWL2.XMLKeywords

import Common.Lexer

import Data.List

import qualified Data.Map as Map

type XMLBase = String

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
isNotSmth q = let qn = qName q in qn `notElem` ["Declaration",
    "Prefix", "Import", "Annotation"]

filterCh :: String -> Element -> [Element]
filterCh s = filterChildrenName (isSmth s)

filterChL :: [String] -> Element -> [Element]
filterChL l = filterChildrenName (isSmthList l)

filterC :: String -> Element -> Element
filterC s e = fromMaybe (error "child not found")
    (filterChildName (isSmth s) e)

filterCL :: [String] -> Element -> Element
filterCL l e = fromMaybe (error "child not found")
    (filterChildName (isSmthList l) e)

simpleSplit :: IRI -> IRI
simpleSplit qn =
    let lp = localPart qn
        lp2 = case lp of
            '_' : ':' : t -> t
            _ -> lp
        ai = case lp of
            '_' : ':' : _ -> "_:"
            _ -> ""
        np = takeWhile (/= ':') lp2
        ':' : nlp = dropWhile (/= ':') lp2
    in qn {namePrefix = ai ++ np, localPart = nlp}

{- if the IRI contains ':', it is split at the colon
else, the xml:base needs to be pre-pended to the addres
and then the IRI must be splitted -}
splitIRI :: XMLBase -> IRI -> IRI
splitIRI b qn =
 let r = localPart qn
 in if ':' `elem` r then simpleSplit qn
     else simpleSplit $ qn {localPart = b ++ r, isFullIri = True}

-- gets the actual name of an axiom in XML Syntax
getName :: Element -> String
getName e =
  let n = (qName . elName) e
      q = (qURI . elName) e
  in case q of
    Just "http://www.w3.org/2002/07/owl#" -> n
    _ -> ""

getIRI :: XMLBase -> Element -> IRI
getIRI b e =
  let [a] = elAttribs e
      iri = attrVal a
      f = if (qName $ attrKey a) == "abbreviatedIRI" then False else True
  in splitIRI b $ nullQName {localPart = iri, isFullIri = f}

getFullOrAbbrIRI :: XMLBase -> Element -> IRI
getFullOrAbbrIRI b e =
  let cont = strContent e
  in case getName e of
      "AbbreviatedIRI" -> simpleSplit $ nullQName {localPart = cont}
      "IRI" -> if ':' `elem` cont then
                 simpleSplit $ nullQName {localPart = cont,
                          isFullIri = True}
                else splitIRI b
                     $ nullQName {localPart = cont}
      _ -> error "invalid type of iri"

getInt :: Element -> Int
getInt e = let [int] = elAttribs e in value 10 $ attrVal int

getEntityType :: String -> EntityType
getEntityType ty = case ty of
    "Class" -> Class
    "Datatype" -> Datatype
    "NamedIndividual" -> NamedIndividual
    "ObjectProperty" -> ObjectProperty
    "DataProperty" -> DataProperty
    "AnnotationProperty" -> AnnotationProperty
    _ -> error "not entity type"

toEntity :: XMLBase -> Element -> Entity
toEntity b e = Entity (getEntityType $ (qName . elName) e) (getIRI b e)

getDeclaration :: XMLBase -> Element -> Axiom
getDeclaration b e = case getName e of
   "Declaration" ->
     let ent = filterCL entityList e
         ans = getAllAnnos b e
         entity@(Entity ty iri) = toEntity b ent
     in case ty of
        AnnotationProperty -> PlainAxiom (Misc ans) $ AnnFrameBit
            [Annotation [] iri $ AnnValue iri] AnnotationFrameBit
        _ -> PlainAxiom (SimpleEntity entity) $ AnnFrameBit ans AnnotationFrameBit
   _ -> error "not declaration"

isPlainLiteral :: String -> Bool
isPlainLiteral s =
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" == s

getLiteral :: Element -> Literal
getLiteral e = case getName e of
    "Literal" ->
      let lf = strContent e
          mdt = findAttr (unqual "datatypeIRI") e
          mattr = vFindAttrBy (isSmth "lang") e
      in case mdt of
          Nothing -> case mattr of
             Just lang -> Literal lf (Untyped $ Just lang)
             Nothing -> Literal lf (Untyped Nothing)
          Just dt -> case mattr of
             Just lang -> Literal lf (Untyped $ Just lang)
             Nothing -> if isPlainLiteral dt then
                          Literal lf (Untyped Nothing)
                         else Literal lf (Typed $ simpleSplit $ mkQName dt)
    _ -> error "not literal"

getValue :: XMLBase -> Element -> AnnotationValue
getValue b e = case getName e of
    "Literal" -> AnnValLit $ getLiteral e
    "AnonymousIndividual" -> AnnValue $ getIRI b e
    _ -> AnnValue $ getFullOrAbbrIRI b e

getSubject :: XMLBase -> Element -> IRI
getSubject b e = case getName e of
    "AnonymousIndividual" -> getIRI b e
    _ -> getFullOrAbbrIRI b e

getAnnotation :: XMLBase -> Element -> Annotation
getAnnotation b e =
     let hd = filterCh "Annotation" e
         [ap] = filterCh "AnnotationProperty" e
         [av] = filterCh "Literal" e ++ filterCh "IRI" e
                  ++ filterCh "AnonymousIndividual" e
                  ++ filterCh "AbbreviatedIRI" e
     in
          Annotation (map (getAnnotation b) hd)
              (getIRI b ap) (getValue b av)

getAllAnnos :: XMLBase -> Element -> [Annotation]
getAllAnnos b e = map (getAnnotation b)
            $ filterCh "Annotation" e

getObjProp :: XMLBase -> Element -> ObjectPropertyExpression
getObjProp b e = case getName e of
  "ObjectProperty" -> ObjectProp $ getIRI b e
  "ObjectInverseOf" ->
    let [ch] = elChildren e
        [cch] = elChildren ch
    in case getName ch of
      "ObjectInverseOf" -> getObjProp b cch
      "ObjectProperty" -> ObjectInverseOf $ ObjectProp $ getIRI b ch
      _ -> error "not objectProperty"
  _ -> error "not objectProperty"

getFacetValuePair :: XMLBase -> Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair b e = case getName e of
    "FacetRestriction" ->
       let [ch] = elChildren e
       in (getIRI b e, getLiteral ch)
    _ -> error "not facet"

getDataRange :: XMLBase -> Element -> DataRange
getDataRange b e =
  let ch@(ch1 : _) = elChildren e
  in case getName e of
    "Datatype" -> DataType (getIRI b e) []
    "DatatypeRestriction" ->
        let dt = getIRI b $ filterC "Datatype" e
            fvp = map (getFacetValuePair b)
               $ filterCh "FacetRestriction" e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf
            $ getDataRange b ch1
    "DataOneOf" -> DataOneOf
            $ map getLiteral $ filterCh "Literal" e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map (getDataRange b) ch
    "DataUnionOf" -> DataJunction UnionOf
            $ map (getDataRange b) ch
    _ -> error "XML parser: not data range"

getClassExpression :: XMLBase -> Element -> ClassExpression
getClassExpression b e =
  let ch@(ch1 : _) = elChildren e
      rch1 : _ = reverse ch
  in case getName e of
    "Class" -> Expression $ getIRI b e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map (getClassExpression b) ch
    "ObjectUnionOf" -> ObjectJunction UnionOf
            $ map (getClassExpression b) ch
    "ObjectComplementOf" -> ObjectComplementOf
            $ getClassExpression b ch1
    "ObjectOneOf" -> ObjectOneOf
            $ map (getIRI b) ch
    "ObjectSomeValuesFrom" -> ObjectValuesFrom SomeValuesFrom
            (getObjProp b ch1) (getClassExpression b rch1)
    "ObjectAllValuesFrom" -> ObjectValuesFrom AllValuesFrom
            (getObjProp b ch1) (getClassExpression b rch1)
    "ObjectHasValue" -> ObjectHasValue (getObjProp b ch1) (getIRI b rch1)
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp b ch1
    "ObjectMinCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp b ch1)
                $ Just $ getClassExpression b rch1
         else ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp b ch1) Nothing
    "ObjectMaxCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp b ch1)
                $ Just $ getClassExpression b rch1
         else ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp b ch1) Nothing
    "ObjectExactCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp b ch1)
                $ Just $ getClassExpression b rch1
         else ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp b ch1) Nothing
    "DataSomeValuesFrom" ->
        let dp = getIRI b ch1
            dr = rch1
        in DataValuesFrom SomeValuesFrom dp (getDataRange b dr)
    "DataAllValuesFrom" ->
        let dp = getIRI b ch1
            dr = rch1
        in DataValuesFrom AllValuesFrom dp (getDataRange b dr)
    "DataHasValue" -> DataHasValue (getIRI b ch1) (getLiteral rch1)
    "DataMinCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI b ch1)
                $ Just $ getDataRange b rch1
         else DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI b ch1) Nothing
    "DataMaxCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI b ch1)
                $ Just $ getDataRange b rch1
         else DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI b ch1) Nothing
    "DataExactCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI b ch1)
                $ Just $ getDataRange b rch1
         else DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI b ch1) Nothing
    _ -> error "XML parser: not ClassExpression"

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
      (Just (EDRelation Equivalent)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just (EDRelation Disjoint)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointUnion" -> PlainAxiom (ClassEntity $ getClassExpression b hd)
        $ AnnFrameBit as $ ClassDisjointUnion $ map (getClassExpression b) tl
    "DatatypeDefinition" -> PlainAxiom (SimpleEntity $ Entity
                Datatype $ getIRI b dhd)
        $ AnnFrameBit as $ DatatypeBit $ getDataRange b dtl
    _ -> hasKey b e

hasKey :: XMLBase -> Element -> Axiom
hasKey b e = case getName e of
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
             then let [hd, lst] = map (getObjProp b)
                        $ filterChL objectPropList e
                  in PlainAxiom (ObjectEntity hd)
                       $ ListFrameBit (Just SubPropertyOf) $ ObjectBit
                          [(as, lst)]
             else PlainAxiom (ObjectEntity op) $ AnnFrameBit as
                    $ ObjectSubPropertyChain opchain
    "EquivalentObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "DisjointObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ADomain)) $ ExpressionBit [(as, ce)]
    "ObjectPropertyRange" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ARange)) $ ExpressionBit [(as, ce)]
    "InverseObjectProperties" ->
       let [hd, lst] = map (getObjProp b) $ filterChL objectPropList e
       in PlainAxiom (ObjectEntity hd)
                       $ ListFrameBit (Just InverseOf) $ ObjectBit
                          [(as, lst)]
    "FunctionalObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Functional)]
    "InverseFunctionalObjectProperty" -> PlainAxiom (ObjectEntity op)
        $ ListFrameBit Nothing $ ObjectCharacteristics [(as, InverseFunctional)]
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
        in PlainAxiom (SimpleEntity $ Entity DataProperty hd)
              $ ListFrameBit (Just SubPropertyOf) $ DataBit [(as, lst)]
    "EquivalentDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DisjointDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DataPropertyDomain" ->
        let dp = getIRI b $ filterCL dataPropList e
            ce = getClassExpression b $ filterCL classExpressionList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit (Just (DRRelation ADomain))
                     $ ExpressionBit [(as, ce)]
    "DataPropertyRange" ->
        let dp = getIRI b $ filterCL dataPropList e
            dr = getDataRange b $ filterCL dataRangeList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit Nothing $ DataPropRange [(as, dr)]
    "FunctionalDataProperty" ->
        let dp = getIRI b $ filterCL dataPropList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ AnnFrameBit as DataFunctional
    _ -> getDataAssertion b e

getDataAssertion :: XMLBase -> Element -> Axiom
getDataAssertion b e =
   let as = getAllAnnos b e
       dp = getIRI b $ filterCL dataPropList e
       ind = getIRI b $ filterCL individualList e
       lit = getLiteral $ filterC "Literal" e
   in case getName e of
    "DataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, DataPropertyFact Positive dp lit)]
    "NegativeDataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
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
        PlainAxiom (SimpleEntity $ Entity NamedIndividual hd)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Positive op lst)]
    "NegativeObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ Entity NamedIndividual hd)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Negative op lst)]
    _ -> getIndividualAssertion b e

getIndividualAssertion :: XMLBase -> Element -> Axiom
getIndividualAssertion b e =
   let as = getAllAnnos b e
       ind = map (getIRI b) $ filterChL individualList e
       l = map (\ x -> ([], x)) ind
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
        in PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit (Just Types) $ ExpressionBit [(as, ce)]
    _ -> getAnnoAxiom b e

getAnnoAxiom :: XMLBase -> Element -> Axiom
getAnnoAxiom b e =
   let as = getAllAnnos b e
       ap = getIRI b $ filterC "AnnotationProperty" e
   in case getName e of
    "AnnotationAssertion" ->
       let [s, v] = filterChL ["AbbreviatedIRI", "IRI",
            "AnonymousIndividual", "Literal"] e
       in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ AnnFrameBit [Annotation as (getSubject b s) (getValue b v)]
                    AnnotationFrameBit
    "SubAnnotationPropertyOf" ->
        let [hd, lst] = map (getIRI b) $ filterCh "AnnotationProperty" e
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty hd)
            $ ListFrameBit (Just SubPropertyOf) $ AnnotationBit [(as, lst)]
    "AnnotationPropertyDomain" ->
        let [ch] = filterChL ["IRI", "AbbreviatedIRI"] e
            iri = getFullOrAbbrIRI b ch
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ ListFrameBit (Just (DRRelation ADomain))
                      $ AnnotationBit [(as, iri)]
    "AnnotationPropertyRange" ->
        let [ch] = filterChL ["IRI", "AbbreviatedIRI"] e
            iri = getFullOrAbbrIRI b ch
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ ListFrameBit (Just (DRRelation ARange))
                      $ AnnotationBit [(as, iri)]
    _ -> error "bad frame"

getImports :: XMLBase -> Element -> [ImportIRI]
getImports b e = map (setFull . splitIRI b . mkQName . strContent)
    $ filterCh "Import" e

-- gets one prefix with the corresponding iri
get1PrefMap :: Element -> (String, IRI)
get1PrefMap e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, setFull $ splitIRI "" $ mkQName pmap)

getPrefixMap :: Element -> [(String, String)]
getPrefixMap e =
    let prl = map get1PrefMap $ filterCh "Prefix" e
    in map (\ (p, m) -> (p, showQU m)) prl

getOntologyIRI :: Element -> OntologyIRI
getOntologyIRI e =
  let oi = findAttr (unqual "ontologyIRI") e
  in case oi of
    Nothing -> dummyQName
    Just iri -> setFull $ splitIRI ""
        $ nullQName {localPart = iri, isFullIri = True}

axToFrame :: Axiom -> Frame
axToFrame (PlainAxiom e fb) = Frame e [fb]

getFrames :: XMLBase -> Element -> [Frame]
getFrames b e =
   let ax = filterChildrenName isNotSmth e
       f = map axToFrame (map (getDeclaration b) (filterCh "Declaration" e))
            ++ map (axToFrame . getClassAxiom b) ax
   in f ++ signToFrames f

getAxioms :: XMLBase -> Element -> [Axiom]
getAxioms b e = map (getClassAxiom b) $ filterChildrenName isNotSmth e

getBase :: Element -> XMLBase
getBase e = fromJust $ vFindAttrBy (isSmth "base") e

xmlBasicSpec :: Element -> OntologyDocument
xmlBasicSpec e = let b = getBase e in emptyOntologyDoc
      {
      ontology = emptyOntologyD
        {
        ontFrames = getFrames b e,
        imports = getImports b e,
        ann = [getAllAnnos b e],
        name = getOntologyIRI e
        },
      prefixDeclaration = Map.fromList $ getPrefixMap e
      }
