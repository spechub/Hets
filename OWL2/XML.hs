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
import qualified Common.GlobalAnnotations as GA (PrefixMap)


import qualified OWL2.AS as AS
import OWL2.Keywords
import OWL2.MS
import OWL2.XMLKeywords

import Text.XML.Light

import Data.Maybe
import Data.List
import qualified Data.Map as Map

type XMLBase = Maybe String

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
isNotSmth q = let qn = qName q in qn `notElem` [
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
getIRI :: GA.PrefixMap -> XMLBase -> Element -> IRI
getIRI pm b e =
    let [a] = elAttribs e
        anIri = attrVal a
    in expandIRI pm $ case qName $ attrKey a of
        "abbreviatedIRI" ->  case parseCurie anIri of
                Just i -> i
                Nothing -> error $ "could not get CURIE from " ++ show anIri
        "IRI" -> let parsed = getIRIWithResolvedBase b anIri in
            maybe (error $ "could not get IRI from " ++ show anIri) id parsed
        "nodeID" -> (mkIRI anIri){isBlankNode = True}
        "facet" -> let parsed = getIRIWithResolvedBase b anIri in
            maybe (error $ "could not get facet from " ++ show anIri) id parsed
        _ -> error $ "wrong qName:" ++ show (attrKey a)


getIRIWithResolvedBase :: XMLBase -> String -> Maybe IRI
getIRIWithResolvedBase b str =
    -- According to https://www.w3.org/TR/2012/REC-owl2-xml-serialization-20121211/#The_Serialization_Syntax
    -- all @IRI@s must be resolved against xml:base. Only doing this
    -- if the iri is relative
    let absIri = parseIRI str
        resolvedIRI = b >>= (parseIRI . ( ++ str))
    in case absIri of
        Just y -> if not $ null $ iriScheme y then Just y else resolvedIRI
        Nothing -> resolvedIRI



-- | splits an IRI at the colon
splitIRI :: IRI -> IRI
splitIRI iri = let 
  i = iriPath iri
  in if isBlankNode iri then mkNodeID iri else 
   case getTokens i of
    [] -> iri
    (tok:ts) ->
      let lp = tokStr tok
          sp = span (/= ':') lp
      in case sp of
         (np, ':' : nlp) -> iri { iriScheme = np ++ ":"
                                , iriPath = i { getTokens = tok { tokStr = nlp } : ts}
                                }
         _ -> iri
         
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
  in nullIRI {iriPath = stringToId cont, isAbbrev = True}

-- | gets the content of an element with name IRI, AbbreviatedIRI or Import
contentIRI :: GA.PrefixMap -> XMLBase -> Element -> IRI
contentIRI pm b e =
  let cont = strContent e
      anIri = nullIRI {iriPath = stringToId cont, isAbbrev = True}
  in expandIRI pm $ case getName e of
      "AbbreviatedIRI" -> splitIRI anIri
      "IRI" -> if ':' `elem` cont
                then splitIRI  anIri 
                else anIri
      "Import" -> anIri 
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

getEntityType :: String -> AS.EntityType
getEntityType ty = fromMaybe (err $ "no entity type " ++ ty)
  . lookup ty $ map (\ e -> (show e, e)) AS.entityTypes

getEntity :: GA.PrefixMap -> XMLBase -> Element -> AS.Entity
getEntity pm b e = AS.mkEntity (getEntityType $ (qName . elName) e) $ getIRI pm b e

getDeclaration :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getDeclaration pm b e = case getName e of
   "Declaration" ->
       AS.Declaration (getAllAnnos pm b e) (getEntity pm b $ filterCL entityList e)
   _ -> getClassAxiom pm b e

isPlainLiteral :: String -> Bool
isPlainLiteral s =
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral" == s

-- | put an "f" for float if not there already (eg. 123.45 --> 123.45f)
correctLit :: AS.Literal -> AS.Literal
correctLit l = case l of
    AS.Literal lf (AS.Typed dt) ->
        let nlf = if isSuffixOf "float" (show $ iriPath dt) && last lf /= 'f'
                then lf ++ "f"
                else lf
        in AS.Literal nlf (AS.Typed dt)
    _ -> l

getLiteral :: GA.PrefixMap -> XMLBase -> Element -> AS.Literal
getLiteral pm b e = case getName e of
    "Literal" ->
      let lf = strContent e
          mdt = findAttr (unqual "datatypeIRI") e
          mattr = vFindAttrBy (isSmth "lang") e
      in case mdt of
          Nothing -> case mattr of
             Just lang -> AS.Literal lf $ AS.Untyped $ Just lang
             Nothing -> AS.Literal lf $ AS.Untyped Nothing
          Just dt -> case mattr of
             Just lang -> AS.Literal lf $ AS.Untyped $ Just lang
             Nothing -> if isPlainLiteral dt then
                          AS.Literal lf $ AS.Untyped Nothing
                         else case parseIRIReference dt of
                            Just f -> correctLit $ AS.Literal lf $ AS.Typed (expandIRI pm f)
                            _ -> error $ "could not get datatypeIRI from " ++ show dt
    _ -> err "not literal"

getValue :: GA.PrefixMap -> XMLBase -> Element -> AS.AnnotationValue
getValue pm b e = case getName e of
    "Literal" -> AS.AnnValLit $ getLiteral pm b e
    "AnonymousIndividual" -> AS.AnnValue $ getIRI pm b e
    _ -> AS.AnnValue $ contentIRI pm b e

getSubject :: GA.PrefixMap -> XMLBase -> Element -> IRI
getSubject pm b e = case getName e of
    "AnonymousIndividual" -> getIRI pm b e
    _ -> contentIRI pm b e

getAnnotation :: GA.PrefixMap -> XMLBase -> Element -> AS.Annotation
getAnnotation pm b e =
     let hd = filterCh "Annotation" e
         [ap] = filterCh "AnnotationProperty" e
         av = filterCL annotationValueList e
     in AS.Annotation (map (getAnnotation pm b) hd) (getIRI pm b ap) $ getValue pm b av

-- | returns a list of annotations
getAllAnnos :: GA.PrefixMap -> XMLBase -> Element -> [AS.Annotation]
getAllAnnos pm b e = map (getAnnotation pm b) $ filterCh "Annotation" e

getObjProp :: GA.PrefixMap -> XMLBase -> Element -> AS.ObjectPropertyExpression
getObjProp pm b e = case getName e of
  "ObjectProperty" -> AS.ObjectProp $ getIRI pm b e
  "ObjectInverseOf" ->
    let [ch] = elChildren e
        [cch] = elChildren ch
    in case getName ch of
      "ObjectInverseOf" -> getObjProp pm b cch
      "ObjectProperty" -> AS.ObjectInverseOf $ AS.ObjectProp $ getIRI pm b ch
      _ -> err "not objectProperty"
  _ -> err "not objectProperty"

-- | replaces eg. "minExclusive" with ">"
properFacet :: AS.ConstrainingFacet -> AS.ConstrainingFacet
properFacet cf
    | hasFullIRI cf =
        let p = showIRICompact cf \\ "http://www.w3.org/2001/XMLSchema#"
        in case p of
            "minInclusive" -> AS.facetToIRI MININCLUSIVE
            "minExclusive" -> AS.facetToIRI MINEXCLUSIVE
            "maxInclusive" -> AS.facetToIRI MAXINCLUSIVE
            "maxExclusive" -> AS.facetToIRI MAXEXCLUSIVE
            _ -> cf
    | otherwise = cf

getFacetValuePair :: GA.PrefixMap -> XMLBase -> Element -> (AS.ConstrainingFacet, AS.RestrictionValue)
getFacetValuePair pm b e = case getName e of
    "FacetRestriction" ->
       let [ch] = elChildren e
       in (properFacet $ getIRI pm b e, getLiteral pm b ch)
    _ -> err "not facet"

getDataRange :: GA.PrefixMap -> XMLBase -> Element -> AS.DataRange
getDataRange pm b e =
  let ch@(ch1 : _) = elChildren e
  in case getName e of
    "Datatype" -> AS.DataType (getIRI pm b e) []
    "DatatypeRestriction" ->
        let dt = getIRI pm b $ filterC "Datatype" e
            fvp = map (getFacetValuePair pm b) $ filterCh "FacetRestriction" e
        in AS.DataType dt fvp
    "DataComplementOf" -> AS.DataComplementOf $ getDataRange pm b ch1
    "DataOneOf" -> AS.DataOneOf $ map (getLiteral pm b) $ filterCh "Literal" e
    "DataIntersectionOf" -> AS.DataJunction AS.IntersectionOf
            $ map (getDataRange pm b) ch
    "DataUnionOf" -> AS.DataJunction AS.UnionOf $ map (getDataRange pm b) ch
    _ -> err "not data range"

getClassExpression :: GA.PrefixMap -> XMLBase -> Element -> AS.ClassExpression
getClassExpression pm b e =
  let ch = elChildren e
      ch1 : _ = ch
      rch1 : _ = reverse ch
  in case getName e of
    "Class" -> AS.Expression $ getIRI pm b e
    "ObjectIntersectionOf" -> AS.ObjectJunction AS.IntersectionOf
            $ map (getClassExpression pm b) ch
    "ObjectUnionOf" -> AS.ObjectJunction AS.UnionOf $ map (getClassExpression pm b) ch
    "ObjectComplementOf" -> AS.ObjectComplementOf $ getClassExpression pm b ch1
    "ObjectOneOf" -> AS.ObjectOneOf $ map (getIRI pm b) ch
    "ObjectSomeValuesFrom" -> AS.ObjectValuesFrom AS.SomeValuesFrom
            (getObjProp pm b ch1) $ getClassExpression pm b rch1
    "ObjectAllValuesFrom" -> AS.ObjectValuesFrom AS.AllValuesFrom
            (getObjProp pm b ch1) $ getClassExpression pm b rch1
    "ObjectHasValue" -> AS.ObjectHasValue (getObjProp pm b ch1) $ getIRI pm b rch1
    "ObjectHasSelf" -> AS.ObjectHasSelf $ getObjProp pm b ch1
    "DataSomeValuesFrom" -> AS.DataValuesFrom AS.SomeValuesFrom ([getIRI pm b ch1])
            $ getDataRange pm b rch1
    "DataAllValuesFrom" -> AS.DataValuesFrom AS.AllValuesFrom ([getIRI pm b ch1])
            $ getDataRange pm b rch1
    "DataHasValue" -> AS.DataHasValue (getIRI pm b ch1) $ getLiteral pm b rch1
    _ -> getObjCard pm b e ch rch1

getObjCard :: GA.PrefixMap -> XMLBase -> Element -> [Element] -> Element -> AS.ClassExpression
getObjCard pm b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        op = getObjProp pm b ch1
        ce = if length ch == 2
                then Just $ getClassExpression pm b rch1
                else Nothing
    in case getName e of
        "ObjectMinCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.MinCardinality i op ce
        "ObjectMaxCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.MaxCardinality i op ce
        "ObjectExactCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.ExactCardinality i op ce
        _ -> getDataCard pm b e ch rch1

getDataCard :: GA.PrefixMap -> XMLBase -> Element -> [Element] -> Element -> AS.ClassExpression
getDataCard pm b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        dp = getIRI pm b ch1
        dr = if length ch == 2
                then Just $ getDataRange pm b rch1
                else Nothing
    in case getName e of
        "DataMinCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.MinCardinality i dp dr
        "DataMaxCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.MaxCardinality i dp dr
        "DataExactCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.ExactCardinality i dp dr
        _ -> err "not class expression"

getClassAxiom :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getClassAxiom pm b e =
   let ch = elChildren e
       as = getAllAnnos pm b e
       l@(hd : tl) = filterChL classExpressionList e
       [dhd, dtl] = filterChL dataRangeList e
       cel = map (getClassExpression pm b) l
   in case getName e of
    "SubClassOf" ->
       let [sub, super] = getClassExpression pm b <$> drop (length ch - 2) ch
       in AS.ClassAxiom $ AS.SubClassOf as sub super
    "EquivalentClasses" -> AS.ClassAxiom $ AS.EquivalentClasses as cel
    "DisjointClasses" -> AS.ClassAxiom $ AS.DisjointClasses as cel
    "DisjointUnion" -> case getClassExpression pm b hd of
        AS.Expression c -> AS.ClassAxiom $ AS.DisjointUnion as c (getClassExpression pm b <$> tl)
        _ -> err "Invalid ClassExpression. DisjointUnion must have a class."
    "DatatypeDefinition" ->
        AS.DatatypeDefinition as (getIRI pm b dhd) (getDataRange pm b dtl)
    _ -> getKey pm b e

getKey :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getKey pm b e = case getName e of
  "HasKey" ->
    let as = getAllAnnos pm b e
        [ce] = filterChL classExpressionList e
        op = map (getObjProp pm b) $ filterChL objectPropList e
        dp = map (getIRI pm b) $ filterChL dataPropList e
    in AS.HasKey as (getClassExpression pm b ce) op dp
  _ -> getOPAxiom pm b e

getOPAxiom :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getOPAxiom pm b e =
   let as = getAllAnnos pm b e
       op = getObjProp pm b $ filterCL objectPropList e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map $ getObjProp pm b) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let [o1, o2] = map (getObjProp pm b) $ filterChL objectPropList e
                  in AS.ObjectPropertyAxiom $ 
                    AS.SubObjectPropertyOf as (AS.SubObjPropExpr_obj o1) o2
             else AS.ObjectPropertyAxiom $ 
                AS.SubObjectPropertyOf as (AS.SubObjPropExpr_exprchain opchain) op
    "EquivalentObjectProperties" ->
       let opl = map (getObjProp pm b) $ filterChL objectPropList e
       in AS.ObjectPropertyAxiom $ 
        AS.EquivalentObjectProperties as opl
    "DisjointObjectProperties" ->
       let opl = map (getObjProp pm b) $ filterChL objectPropList e
       in AS.ObjectPropertyAxiom $ 
        AS.DisjointObjectProperties as opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression pm b $ filterCL classExpressionList e
       in AS.ObjectPropertyAxiom $ 
        AS.ObjectPropertyDomain as op ce
    "ObjectPropertyRange" ->
       let ce = getClassExpression pm b $ filterCL classExpressionList e
       in AS.ObjectPropertyAxiom $ 
        AS.ObjectPropertyRange as op ce
    "InverseObjectProperties" ->
       let [hd, lst] = map (getObjProp pm b) $ filterChL objectPropList e
       in AS.ObjectPropertyAxiom $ 
        AS.InverseObjectProperties as hd lst
    "FunctionalObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.FunctionalObjectProperty as op
    "InverseFunctionalObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.InverseFunctionalObjectProperty as op
    "ReflexiveObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.ReflexiveObjectProperty as op
    "IrreflexiveObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.IrreflexiveObjectProperty as op
    "SymmetricObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.SymmetricObjectProperty as op
    "AsymmetricObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.AsymmetricObjectProperty as op
    "TransitiveObjectProperty" -> AS.ObjectPropertyAxiom $ 
        AS.TransitiveObjectProperty as op
    _ -> getDPAxiom pm b e

getDPAxiom :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getDPAxiom pm b e =
   let as = getAllAnnos pm b e
   in case getName e of
    "SubDataPropertyOf" ->
        let [hd, lst] = map (getIRI pm b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.SubDataPropertyOf as hd lst
    "EquivalentDataProperties" ->
        let dpl = map (getIRI pm b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.EquivalentDataProperties as dpl
    "DisjointDataProperties" ->
        let dpl = map (getIRI pm b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.DisjointDataProperties as dpl
    "DataPropertyDomain" ->
        let dp = getIRI pm b $ filterCL dataPropList e
            ce = getClassExpression pm b $ filterCL classExpressionList e
        in AS.DataPropertyAxiom $ AS.DataPropertyDomain as dp ce
    "DataPropertyRange" ->
        let dp = getIRI pm b $ filterCL dataPropList e
            dr = getDataRange pm b $ filterCL dataRangeList e
        in AS.DataPropertyAxiom $ AS.DataPropertyRange as dp dr
    "FunctionalDataProperty" ->
        let dp = getIRI pm b $ filterCL dataPropList e
        in AS.DataPropertyAxiom $ AS.FunctionalDataProperty as dp
    _ -> getDataAssertion pm b e

getDataAssertion :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getDataAssertion pm b e =
   let as = getAllAnnos pm b e
       dp = getIRI pm b $ filterCL dataPropList e
       ind = getIRI pm b $ filterCL individualList e
       lit = getLiteral pm b $ filterC "Literal" e
   in case getName e of
    "DataPropertyAssertion" -> AS.Assertion $ AS.DataPropertyAssertion as dp ind lit
    "NegativeDataPropertyAssertion" -> 
        AS.Assertion $  AS.NegativeDataPropertyAssertion as dp ind lit
    _ -> getObjectAssertion pm b e


getObjectAssertion :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getObjectAssertion pm b e =
   let as = getAllAnnos pm b e
       op = getObjProp pm b $ filterCL objectPropList e
       [hd, lst] = map (getIRI pm b) $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" -> AS.Assertion $ AS.ObjectPropertyAssertion as op hd lst
    "NegativeObjectPropertyAssertion" ->
        AS.Assertion $ AS.NegativeObjectPropertyAssertion as op hd lst
    _ -> getIndividualAssertion pm b e

getIndividualAssertion :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getIndividualAssertion pm b e =
   let as = getAllAnnos pm b e
       ind = map (getIRI pm b) $ filterChL individualList e
   in case getName e of
    "SameIndividual" -> AS.Assertion $ AS.SameIndividual as ind
    "DifferentIndividuals" -> AS.Assertion $ AS.DifferentIndividuals as ind
    _ -> getClassAssertion pm b e

getClassAssertion :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getClassAssertion pm b e = case getName e of
    "ClassAssertion" ->
        let as = getAllAnnos pm b e
            ce = getClassExpression pm b $ filterCL classExpressionList e
            ind = getIRI pm b $ filterCL individualList e
        in AS.Assertion $ AS.ClassAssertion as ce ind
    _ -> getAnnoAxiom pm b e

getAnnoAxiom :: GA.PrefixMap -> XMLBase -> Element -> AS.Axiom
getAnnoAxiom pm b e =
   let as = getAllAnnos pm b e
       ap = getIRI pm b $ filterC "AnnotationProperty" e
       [ch] = filterChL [iriK, abbreviatedIRI] e
       anIri = contentIRI pm b ch
    in case getName e of
    "AnnotationAssertion" ->
       let [s, v] = filterChL annotationValueList e
           sub = getSubject pm b s
        -- TODO: What about iris?
       in AS.AnnotationAxiom $ AS.AnnotationAssertion as ap (AS.AnnSubIri sub) (getValue pm b v)
       -- the misc will be converted to entities in static analysis
    --    in PlainAxiom (Misc [AS.Annotation [] sub $ AS.AnnValue sub])
    --        $ AnnFrameBit [AS.Annotation as ap (getValue b v)]
    --                 $ AnnotationFrameBit Assertion
    "SubAnnotationPropertyOf" ->
        let [hd, lst] = map (getIRI pm b) $ filterCh "AnnotationProperty" e
        in AS.AnnotationAxiom $ AS.SubAnnotationPropertyOf as hd lst
    "AnnotationPropertyDomain" -> AS.AnnotationAxiom $ AS.AnnotationPropertyDomain as ap anIri
    "AnnotationPropertyRange" -> AS.AnnotationAxiom $ AS.AnnotationPropertyRange as ap anIri
    s -> err $ "Unexpected element '" ++ s ++ "'."

xmlErrorString :: Axiom -> Maybe String
xmlErrorString a = case a of
   PlainAxiom (Misc []) (AnnFrameBit [] (AnnotationFrameBit (XmlError e)))
     -> Just e
   _ -> Nothing


getOnlyAxioms :: GA.PrefixMap -> XMLBase -> Element -> [AS.Axiom]
getOnlyAxioms pm b e = map (getDeclaration pm b) $ filterChildrenName isNotSmth e

getImports :: Map.Map String String -> XMLBase -> Element -> AS.DirectlyImportsDocuments
getImports m b e = map (importIRI m b) $ filterCh importK e

get1Map :: Element -> (String, String)
get1Map e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, pmap)

getPrefixMap :: Element -> GA.PrefixMap
getPrefixMap e = AS.changePrefixMapTypeToGA $ Map.map (\x -> "<" ++ x ++ ">") $ Map.fromList $ map get1Map $ filterCh "Prefix" e

getOntologyIRI :: XMLBase -> Element -> Maybe IRI
getOntologyIRI b e =
  let oi = findAttr (unqual "ontologyIRI") e
  in fmap (\anIri -> nullIRI {iriPath = stringToId anIri}) oi

getVersionIRI :: XMLBase -> Element -> Maybe IRI
getVersionIRI b e =
  let oi = findAttr (unqual "versionIRI") e
  in fmap (\anIri -> nullIRI {iriPath = stringToId anIri}) oi

getBase :: Element -> XMLBase
getBase e = vFindAttrBy (isSmth "base") e

-- | parses an ontology document
xmlBasicSpec :: Map.Map String String -> Element -> AS.OntologyDocument
xmlBasicSpec imap e =
    let b = getBase e
        pm = getPrefixMap e
        ax = getOnlyAxioms (AS.changePrefixMapTypeToGA imap `Map.union` pm) b e
    in
        AS.OntologyDocument
            (AS.OntologyMetadata AS.XML)
            (getPrefixMap e)
            $ AS.Ontology
                (getOntologyIRI b e)
                (getVersionIRI b e)
                (getImports imap b e)
                (getAllAnnos pm b e)
                ax
