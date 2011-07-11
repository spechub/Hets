{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 XML Syntax Parsing
-}

{- still left to do:
     - cancel multiple inverses for object properties
     - separate qnames at the colon
     - include all prefixes, xml-type
     - simplify some functions
      -}
module OWL2.XML where

import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS
import Common.Lexer

import Data.List

import qualified Data.Map as Map

splitIRI :: IRI -> IRI
splitIRI qn =
  let QN {localPart = s} = qn
  in let r = delete '<' $ delete '>' $ delete '&' $ delete '#' s
     in
       if elem ':' r then
          let p = takeWhile (/= ':') r
              lp = drop (length p + 1) r
          in nullQName {namePrefix = p, localPart = lp, isFullIri =
                if r == s then False else True}
        else qn {localPart = r}

getName :: Element -> String
getName e =
  let n = (qName . elName) e
      q = (qURI . elName) e
  in case q of
    Just "http://www.w3.org/2002/07/owl#" -> n
    _ -> ""

getIRI :: Element -> OWL2.AS.QName
getIRI e = let [a] = elAttribs e in splitIRI $ mkQName $ attrVal a

get1PrefMap :: Element -> (String, IRI)
get1PrefMap e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, splitIRI $ mkQName pmap)

getInt :: Element -> Int
getInt e = let [int] = elAttribs e in value 10 $ attrVal int  

isSmth :: String -> Text.XML.Light.QName -> Bool
isSmth s = (s == ) . qName 

isSmthList :: [String] -> Text.XML.Light.QName -> Bool
isSmthList l qn = qName qn `elem` l 

isNotSmth :: Text.XML.Light.QName -> Bool
isNotSmth q = let qn = qName q in qn /= "Declaration" &&
    qn /= "Prefix" && qn /= "Import" && qn /= "Annotation"

filterCh :: String -> Element -> [Element]
filterCh s = filterChildrenName (isSmth s)

filterChL :: [String] -> Element -> [Element]
filterChL l = filterChildrenName (isSmthList l)

filterC :: String -> Element -> Element
filterC s e = fromJust $ filterChildName (isSmth s) e

filterCL :: [String] -> Element -> Element
filterCL l e = fromJust $ filterChildName (isSmthList l) e

entityList :: [String]
entityList = ["Class", "Datatype", "NamedIndividual",
    "ObjectProperty", "DataProperty", "AnnotationProperty"]

individualList :: [String]
individualList = ["NamedIndividual", "AnonymousIndividual"]

objectPropList :: [String]
objectPropList = ["ObjectProperty", "ObjectInverseOf"]

dataPropList :: [String]
dataPropList = ["DataProperty"]

dataRangeList :: [String]
dataRangeList = ["Datatype", "DatatypeRestriction", "DataComplementOf",
      "DataOneOf", "DataIntersectionOf", "DataUnionOf"]

classExpressionList :: [String]
classExpressionList = ["Class", "ObjectIntersectionOf", "ObjectUnionOf",
     "ObjectComplementOf", "ObjectOneOf", "ObjectSomeValuesFrom",
     "ObjectAllValuesFrom", "ObjectHasValue", "ObjectHasSelf",
     "ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality",
     "DataSomeValuesFrom", "DataAllValuesFrom", "DataHasValue",
     "DataMinCardinality", "DataMaxCardinality", "DataExactCardinality"]

getEntityType :: String -> EntityType
getEntityType ty = case ty of
    "Class" -> Class
    "Datatype" -> Datatype
    "NamedIndividual" -> NamedIndividual
    "ObjectProperty" -> ObjectProperty
    "DataProperty" -> DataProperty
    "AnnotationProperty" -> AnnotationProperty
    _ -> error "not entity type"

toEntity :: Element -> Entity
toEntity e = Entity (getEntityType $ getName e) (getIRI e)

getEntity :: Element -> Entity
getEntity e = toEntity $ fromJust $ filterElementName (isSmthList entityList) e

getDeclaration :: Element -> Frame
getDeclaration e =
   let ent = filterCL entityList e
       ans = getAllAnnos e
   in Frame (SimpleEntity $ toEntity ent) [AnnFrameBit ans AnnotationFrameBit]

getDeclarations :: Element -> [Frame]
getDeclarations e =
   let dcl = filterElementsName (isSmth "Declaration") e
   in map getDeclaration dcl

isPlainLiteral :: String -> Bool
isPlainLiteral s = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" == s

getLiteral :: Element -> Literal
getLiteral e = let lit = fromJust $ filterElementName (isSmth "Literal") e
                   lf = strContent e
                   mdt = findAttr (unqual "datatypeIRI") lit
                   mattr = findAttr (unqual "lang") lit
               in case mdt of
                    Nothing -> case mattr of
                      Just lang -> Literal lf (Untyped $ Just lang)
                      Nothing -> Literal lf (Untyped Nothing)
                    Just dt -> case mattr of
                      Just lang -> Literal lf (Untyped $ Just lang)
                      Nothing -> if isPlainLiteral dt then
                                      Literal lf (Untyped Nothing)
                                  else Literal lf (Typed $ splitIRI $ mkQName dt)

getValue :: Element -> AnnotationValue
getValue e = let lit = filterElementName (isSmth "Literal") e
                 val = strContent e
             in case lit of
                  Nothing -> AnnValue $ splitIRI $ mkQName val
                  Just _ -> AnnValLit $ getLiteral e

getAnnotation :: Element -> Annotation
getAnnotation e =
     let hd = filterCh "Annotation" e
         ap = filterCh "AnnotationProperty" e
         av = filterCh "Literal" e ++ filterCh "IRI" e
     in
          Annotation (getAnnotations hd)
              (getIRI $ head ap) (getValue $ head av)

getAnnotations :: [Element] -> [Annotation]
getAnnotations e = map getAnnotation $ concatMap
            (filterElementsName (isSmth "Annotation")) e

getAllAnnos :: Element -> [Annotation]
getAllAnnos e = map getAnnotation
            $ filterElementsName (isSmth "Annotation") e

 -- still need to cancel double inverses
getObjProp :: Element -> ObjectPropertyExpression
getObjProp e = case filterElementName (isSmth "ObjectInverseOf") e of
                  Nothing -> ObjectProp $ getIRI e
                  Just _ -> ObjectInverseOf $ getObjProp $ head $ elChildren e

getFacetValuePair :: Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair e = (getIRI e, getLiteral $ head $ elChildren e)

getDataRange :: Element -> DataRange
getDataRange e = case getName e of
    "Datatype" -> DataType (getIRI e) []
    "DatatypeRestriction" ->
        let dt = getIRI $ filterC "Datatype" e
            fvp = map getFacetValuePair
               $ filterCh "FacetRestriction" e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf
            $ getDataRange $ head $ elChildren e
    "DataOneOf" -> DataOneOf
            $ map getLiteral $ filterCh "Literal" e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map getDataRange $ elChildren e
    "DataUnionOf" -> DataJunction UnionOf
            $ map getDataRange $ elChildren e
    _ -> error "XML parser: not data range"

getClassExpression :: Element -> ClassExpression
getClassExpression e =
  let ch = elChildren e
  in case getName e of
    "Class" -> Expression $ getIRI e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map getClassExpression ch
    "ObjectUnionOf" -> ObjectJunction UnionOf
            $ map getClassExpression ch
    "ObjectComplementOf" -> ObjectComplementOf
            $ getClassExpression $ head ch
    "ObjectOneOf" -> ObjectOneOf
            $ map getIRI ch
    "ObjectSomeValuesFrom" -> ObjectValuesFrom SomeValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectAllValuesFrom" -> ObjectValuesFrom AllValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectHasValue" -> ObjectHasValue (getObjProp $ head ch) (getIRI $ last ch)
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp $ head ch
    "ObjectMinCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectMaxCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectExactCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch) Nothing
    "DataSomeValuesFrom" ->
        let dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom SomeValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataAllValuesFrom" ->
        let dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom AllValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataHasValue" -> DataHasValue (getIRI $ head ch) (getLiteral $ last ch)
    "DataMinCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataMaxCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataExactCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch) Nothing
    _ -> error "XML parser: not ClassExpression"

getClassAxiom :: Element -> Axiom
getClassAxiom e =
   let ch = elChildren e
       as = concatMap getAllAnnos ch
       l@(hd : tl) = filterChL classExpressionList e
       drl@[dhd, dtl] = filterChL dataRangeList e
       cel = map getClassExpression l
   in case getName e of
    "SubClassOf" ->
       let [sub, super] = drop (length ch - 2) ch
       in PlainAxiom (ClassEntity $ getClassExpression sub)
        $ ListFrameBit (Just SubClass) $ ExpressionBit
                      [(as, getClassExpression super)]
    "EquivalentClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just (EDRelation Equivalent)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just (EDRelation Disjoint)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointUnion" -> PlainAxiom (ClassEntity $ getClassExpression hd)
        $ AnnFrameBit as $ ClassDisjointUnion $ map getClassExpression tl
    "DatatypeDefinition" -> PlainAxiom (ClassEntity $ getClassExpression dhd)
        $ AnnFrameBit as $ DatatypeBit $ getDataRange dtl
    _ -> hasKey e

hasKey :: Element -> Axiom
hasKey e = case getName e of
  "HasKey" ->
    let as = concatMap getAllAnnos $ elChildren e
        ce = getClassExpression $ head $ filterChL classExpressionList e
        op = map getObjProp $ filterChL objectPropList e
        dp = map getIRI $ filterChL dataPropList e
    in PlainAxiom (ClassEntity ce) $ AnnFrameBit as $ ClassHasKey op dp
  _ -> getOPAxiom e

getOPAxiom :: Element -> Axiom
getOPAxiom e =
   let as = concatMap getAllAnnos $ elChildren e
       op = getObjProp $ filterCL objectPropList e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map getObjProp) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let opl = map getObjProp $ filterChL objectPropList e
                  in PlainAxiom (ObjectEntity $ head opl)
                       $ ListFrameBit (Just SubPropertyOf) $ ObjectBit
                          [(as, last opl)]
             else PlainAxiom (ObjectEntity op) $ AnnFrameBit as
                    $ ObjectSubPropertyChain opchain
    "EquivalentObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "DisjointObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ADomain)) $ ExpressionBit [(as, ce)]
    "ObjectPropertyRange" ->
       let ce = getClassExpression $ filterCL classExpressionList e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ARange)) $ ExpressionBit [(as, ce)]
    "InverseObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (ObjectEntity $ head opl)
                       $ ListFrameBit (Just InverseOf) $ ObjectBit
                          [(as, last opl)]
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
    "TransitiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Transitive)]
    _ -> getDPAxiom e

getDPAxiom :: Element -> Axiom
getDPAxiom e =
   let as = concatMap getAllAnnos $ elChildren e
   in case getName e of
    "SubDataPropertyOf" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty $ head dpl)
              $ ListFrameBit (Just SubPropertyOf) $ DataBit [(as, last dpl)]
    "EquivalentDataProperties" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DisjointDataProperties" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DataPropertyDomain" ->
        let dp = getIRI $ filterCL dataPropList e
            ce = getClassExpression $ filterCL classExpressionList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit (Just (DRRelation ADomain))
                     $ ExpressionBit [(as, ce)]
    "DataPropertyRange" ->
        let dp = getIRI $ filterCL dataPropList e
            dr = getDataRange $ filterCL dataRangeList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit Nothing $ DataPropRange [(as, dr)]
    "FunctionalDataProperty" ->
        let dp = getIRI $ filterCL dataPropList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ AnnFrameBit as DataFunctional
    _ -> getDataAssertion e

getDataAssertion :: Element -> Axiom
getDataAssertion e =
   let as = concatMap getAllAnnos $ elChildren e
       dp = getIRI $ filterCL dataPropList e
       ind = getIRI $ filterCL individualList e
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
    _ -> getObjectAssertion e

getObjectAssertion :: Element -> Axiom
getObjectAssertion e =
   let as = concatMap getAllAnnos $ elChildren e
       op = getObjProp $ filterCL  objectPropList e
       ind = map getIRI $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ Entity NamedIndividual $ head ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Positive op (last ind))]
    "NegativeObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ Entity NamedIndividual $ head ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Negative op (last ind))]
    _ -> getIndividualAssertion e

getIndividualAssertion :: Element -> Axiom
getIndividualAssertion e =
   let as = concatMap getAllAnnos $ elChildren e
       ind = map getIRI $ filterChL individualList e
       l = map (\ x -> ([], x)) ind
   in case getName e of
    "SameIndividual" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Same))
          $ IndividualSameOrDifferent l
    "DifferentIndividuals" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Different))
          $ IndividualSameOrDifferent l
    _ -> getClassAssertion e

getClassAssertion :: Element -> Axiom
getClassAssertion e = case getName e of
    "ClassAssertion" ->
        let as = concatMap getAllAnnos $ elChildren e
            ce = getClassExpression $ filterCL classExpressionList e
            ind = getIRI $ filterCL individualList e
        in PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit (Just Types) $ ExpressionBit [(as, ce)]
    _ -> getAnnoAxiom e

getAnnoAxiom :: Element -> Axiom
getAnnoAxiom e =
   let as = concatMap getAllAnnos $ elChildren e
       ap = getIRI $ filterC "AnnotationProperty" e
   in case getName e of
    "AnnotationAssertion" ->
       let s = splitIRI $ mkQName $ strContent $ filterC "IRI" e
           v = getValue $ filterC "Literal" e
       in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ AnnFrameBit [Annotation as s v] AnnotationFrameBit
    "SubAnnotationPropertyOf" ->
        let apl = map getIRI $ filterCh "AnnotationProperty" e
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty $ head apl)
            $ ListFrameBit (Just SubPropertyOf) $ AnnotationBit [(as, last apl)]
    "AnnotationPropertyDomain" ->
        let iri = splitIRI $ mkQName $ strContent $ filterC "IRI" e
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ ListFrameBit (Just (DRRelation ADomain))
                      $ AnnotationBit [(as, iri)]
    "AnnotationPropertyRange" ->
        let iri = splitIRI $ mkQName $ strContent $ filterC "IRI" e
        in PlainAxiom (SimpleEntity $ Entity AnnotationProperty ap)
               $ ListFrameBit (Just (DRRelation ARange))
                      $ AnnotationBit [(as, iri)]
    _ -> getClassAxiom e

getImports :: Element -> [ImportIRI]
getImports e = map (splitIRI . mkQName . strContent) $ filterCh "Import" e

getPrefixMap :: Element -> PrefixMap
getPrefixMap e =
    let prl = map get1PrefMap $ filterCh "Prefix" e
    in Map.fromList $ map (\ (p, m) -> (p, showQU m)) prl

getOntologyIRI :: Element -> OntologyIRI
getOntologyIRI e =
  let oi = findAttr (unqual "ontologyIRI") e 
  in case oi of
    Nothing -> dummyQName
    Just iri -> splitIRI $ mkQName iri

getOntAnnos :: Element -> [Annotations]
getOntAnnos e = map getAllAnnos $ filterCh "Annotation" e

axToFrame :: Axiom -> Frame
axToFrame (PlainAxiom e fb) = Frame e [fb]

getFrames :: Element -> [Frame]
getFrames e =
   let ax = filterChildrenName isNotSmth e
   in getDeclarations e ++ map (axToFrame . getClassAxiom) ax

getAxioms :: Element -> [Axiom]
getAxioms e = map getClassAxiom $ filterChildrenName isNotSmth e

xmlBasicSpec :: Element -> OntologyDocument
xmlBasicSpec e = emptyOntologyDoc
      {
      mOntology = emptyOntologyD
        {
        ontologyFrame = getFrames e,
        imports = getImports e,
        ann = getOntAnnos e,
        muri = getOntologyIRI e
        },
      prefixDeclaration = getPrefixMap e
      }
