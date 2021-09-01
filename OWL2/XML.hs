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
        "abbreviatedIRI" ->  
          let (p, _:v) = span (/= ':') anIri
          in appendBase b $ nullIRI {iriPath = stringToId v, prefixName = p, isAbbrev = True }
        "IRI" -> let x = parseIRIReference anIri -- todo: or combine parseIRI and parseIRIReference
                 in case x of
                     Just y -> appendBase b y
                     Nothing -> error $ "could not get IRI from " ++ show anIri
        "nodeID" -> appendBase b $ (mkIRI anIri){isBlankNode = True}
        _ -> error $ "wrong qName:" ++ show (attrKey a)
   

{- | if the IRI contains colon, it is spglit there;
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

getEntityType :: String -> AS.EntityType
getEntityType ty = fromMaybe (err $ "no entity type " ++ ty)
  . lookup ty $ map (\ e -> (show e, e)) AS.entityTypes

getEntity :: XMLBase -> Element -> AS.Entity
getEntity b e = AS.mkEntity (getEntityType $ (qName . elName) e) $ getIRI b e

getDeclaration :: XMLBase -> Element -> AS.Axiom
getDeclaration b e = case getName e of
   "Declaration" ->
       AS.Declaration (getAllAnnos b e) (getEntity b $ filterCL entityList e)
   _ -> getClassAxiom b e

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

getLiteral :: XMLBase -> Element -> AS.Literal
getLiteral b e = case getName e of
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
                         else correctLit $ AS.Literal lf $ AS.Typed $ appendBase b $
                            nullIRI{iriPath = stringToId dt}
    _ -> err "not literal"

getValue :: XMLBase -> Element -> AS.AnnotationValue
getValue b e = case getName e of
    "Literal" -> AS.AnnValLit $ getLiteral b e
    "AnonymousIndividual" -> AS.AnnValue $ getIRI b e
    _ -> AS.AnnValue $ contentIRI b e

getSubject :: XMLBase -> Element -> IRI
getSubject b e = case getName e of
    "AnonymousIndividual" -> getIRI b e
    _ -> contentIRI b e

getAnnotation :: XMLBase -> Element -> AS.Annotation
getAnnotation b e =
     let hd = filterCh "Annotation" e
         [ap] = filterCh "AnnotationProperty" e
         av = filterCL annotationValueList e
     in AS.Annotation (map (getAnnotation b) hd) (getIRI b ap) $ getValue b av

-- | returns a list of annotations
getAllAnnos :: XMLBase -> Element -> [AS.Annotation]
getAllAnnos b e = map (getAnnotation b) $ filterCh "Annotation" e

getObjProp :: XMLBase -> Element -> AS.ObjectPropertyExpression
getObjProp b e = case getName e of
  "ObjectProperty" -> AS.ObjectProp $ getIRI b e
  "ObjectInverseOf" ->
    let [ch] = elChildren e
        [cch] = elChildren ch
    in case getName ch of
      "ObjectInverseOf" -> getObjProp b cch
      "ObjectProperty" -> AS.ObjectInverseOf $ AS.ObjectProp $ getIRI b ch
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

getFacetValuePair :: XMLBase -> Element -> (AS.ConstrainingFacet, AS.RestrictionValue)
getFacetValuePair b e = case getName e of
    "FacetRestriction" ->
       let [ch] = elChildren e
       in (properFacet $ getIRI b e, getLiteral b ch)
    _ -> err "not facet"

getDataRange :: XMLBase -> Element -> AS.DataRange
getDataRange b e =
  let ch@(ch1 : _) = elChildren e
  in case getName e of
    "Datatype" -> AS.DataType (getIRI b e) []
    "DatatypeRestriction" ->
        let dt = getIRI b $ filterC "Datatype" e
            fvp = map (getFacetValuePair b) $ filterCh "FacetRestriction" e
        in AS.DataType dt fvp
    "DataComplementOf" -> AS.DataComplementOf $ getDataRange b ch1
    "DataOneOf" -> AS.DataOneOf $ map (getLiteral b) $ filterCh "Literal" e
    "DataIntersectionOf" -> AS.DataJunction AS.IntersectionOf
            $ map (getDataRange b) ch
    "DataUnionOf" -> AS.DataJunction AS.UnionOf $ map (getDataRange b) ch
    _ -> err "not data range"

getClassExpression :: XMLBase -> Element -> AS.ClassExpression
getClassExpression b e =
  let ch = elChildren e
      ch1 : _ = ch
      rch1 : _ = reverse ch
  in case getName e of
    "Class" -> AS.Expression $ getIRI b e
    "ObjectIntersectionOf" -> AS.ObjectJunction AS.IntersectionOf
            $ map (getClassExpression b) ch
    "ObjectUnionOf" -> AS.ObjectJunction AS.UnionOf $ map (getClassExpression b) ch
    "ObjectComplementOf" -> AS.ObjectComplementOf $ getClassExpression b ch1
    "ObjectOneOf" -> AS.ObjectOneOf $ map (getIRI b) ch
    "ObjectSomeValuesFrom" -> AS.ObjectValuesFrom AS.SomeValuesFrom
            (getObjProp b ch1) $ getClassExpression b rch1
    "ObjectAllValuesFrom" -> AS.ObjectValuesFrom AS.AllValuesFrom
            (getObjProp b ch1) $ getClassExpression b rch1
    "ObjectHasValue" -> AS.ObjectHasValue (getObjProp b ch1) $ getIRI b rch1
    "ObjectHasSelf" -> AS.ObjectHasSelf $ getObjProp b ch1
    "DataSomeValuesFrom" -> AS.DataValuesFrom AS.SomeValuesFrom ([getIRI b ch1])
            $ getDataRange b rch1
    "DataAllValuesFrom" -> AS.DataValuesFrom AS.AllValuesFrom ([getIRI b ch1])
            $ getDataRange b rch1
    "DataHasValue" -> AS.DataHasValue (getIRI b ch1) $ getLiteral b rch1
    _ -> getObjCard b e ch rch1

getObjCard :: XMLBase -> Element -> [Element] -> Element -> AS.ClassExpression
getObjCard b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        op = getObjProp b ch1
        ce = if length ch == 2
                then Just $ getClassExpression b rch1
                else Nothing
    in case getName e of
        "ObjectMinCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.MinCardinality i op ce
        "ObjectMaxCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.MaxCardinality i op ce
        "ObjectExactCardinality" -> AS.ObjectCardinality $ AS.Cardinality
            AS.ExactCardinality i op ce
        _ -> getDataCard b e ch rch1

getDataCard :: XMLBase -> Element -> [Element] -> Element -> AS.ClassExpression
getDataCard b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        dp = getIRI b ch1
        dr = if length ch == 2
                then Just $ getDataRange b rch1
                else Nothing
    in case getName e of
        "DataMinCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.MinCardinality i dp dr
        "DataMaxCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.MaxCardinality i dp dr
        "DataExactCardinality" -> AS.DataCardinality $ AS.Cardinality
              AS.ExactCardinality i dp dr
        _ -> err "not class expression"

getClassAxiom :: XMLBase -> Element -> AS.Axiom
getClassAxiom b e =
   let ch = elChildren e
       as = getAllAnnos b e
       l@(hd : tl) = filterChL classExpressionList e
       [dhd, dtl] = filterChL dataRangeList e
       cel = map (getClassExpression b) l
   in case getName e of
    "SubClassOf" ->
       let [sub, super] = getClassExpression b <$> drop (length ch - 2) ch
       in AS.ClassAxiom $ AS.SubClassOf as sub super
    "EquivalentClasses" -> AS.ClassAxiom $ AS.EquivalentClasses as cel
    "DisjointClasses" -> AS.ClassAxiom $ AS.DisjointClasses as cel
    "DisjointUnion" -> case getClassExpression b hd of
        AS.Expression c -> AS.ClassAxiom $ AS.DisjointUnion as c (getClassExpression b <$> tl)
        _ -> err "Invalid ClassExpression. DisjointUnion must have a class."
    "DatatypeDefinition" ->
        AS.DatatypeDefinition as (getIRI b dhd) (getDataRange b dtl)
    _ -> getKey b e

getKey :: XMLBase -> Element -> AS.Axiom
getKey b e = case getName e of
  "HasKey" ->
    let as = getAllAnnos b e
        [ce] = filterChL classExpressionList e
        op = map (getObjProp b) $ filterChL objectPropList e
        dp = map (getIRI b) $ filterChL dataPropList e
    in AS.HasKey as (getClassExpression b ce) op dp
  _ -> getOPAxiom b e

getOPAxiom :: XMLBase -> Element -> AS.Axiom
getOPAxiom b e =
   let as = getAllAnnos b e
       op = getObjProp b $ filterCL objectPropList e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map $ getObjProp b) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let [o1, o2] = map (getObjProp b) $ filterChL objectPropList e
                  in AS.ObjectPropertyAxiom $ 
                    AS.SubObjectPropertyOf as (AS.SubObjPropExpr_obj o1) o2
             else AS.ObjectPropertyAxiom $ 
                AS.SubObjectPropertyOf as (AS.SubObjPropExpr_exprchain opchain) op
    "EquivalentObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in AS.ObjectPropertyAxiom $ 
        AS.EquivalentObjectProperties as opl
    "DisjointObjectProperties" ->
       let opl = map (getObjProp b) $ filterChL objectPropList e
       in AS.ObjectPropertyAxiom $ 
        AS.DisjointObjectProperties as opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in AS.ObjectPropertyAxiom $ 
        AS.ObjectPropertyDomain as op ce
    "ObjectPropertyRange" ->
       let ce = getClassExpression b $ filterCL classExpressionList e
       in AS.ObjectPropertyAxiom $ 
        AS.ObjectPropertyRange as op ce
    "InverseObjectProperties" ->
       let [hd, lst] = map (getObjProp b) $ filterChL objectPropList e
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
    _ -> getDPAxiom b e

getDPAxiom :: XMLBase -> Element -> AS.Axiom
getDPAxiom b e =
   let as = getAllAnnos b e
   in case getName e of
    "SubDataPropertyOf" ->
        let [hd, lst] = map (getIRI b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.SubDataPropertyOf as hd lst
    "EquivalentDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.EquivalentDataProperties as dpl
    "DisjointDataProperties" ->
        let dpl = map (getIRI b) $ filterChL dataPropList e
        in AS.DataPropertyAxiom $ AS.DisjointDataProperties as dpl
    "DataPropertyDomain" ->
        let dp = getIRI b $ filterCL dataPropList e
            ce = getClassExpression b $ filterCL classExpressionList e
        in AS.DataPropertyAxiom $ AS.DataPropertyDomain as dp ce
    "DataPropertyRange" ->
        let dp = getIRI b $ filterCL dataPropList e
            dr = getDataRange b $ filterCL dataRangeList e
        in AS.DataPropertyAxiom $ AS.DataPropertyRange as dp dr
    "FunctionalDataProperty" ->
        let dp = getIRI b $ filterCL dataPropList e
        in AS.DataPropertyAxiom $ AS.FunctionalDataProperty as dp
    _ -> getDataAssertion b e

getDataAssertion :: XMLBase -> Element -> AS.Axiom
getDataAssertion b e =
   let as = getAllAnnos b e
       dp = getIRI b $ filterCL dataPropList e
       ind = getIRI b $ filterCL individualList e
       lit = getLiteral b $ filterC "Literal" e
   in case getName e of
    "DataPropertyAssertion" -> AS.Assertion $ AS.DataPropertyAssertion as dp ind lit
    "NegativeDataPropertyAssertion" -> 
        AS.Assertion $  AS.NegativeDataPropertyAssertion as dp ind lit
    _ -> getObjectAssertion b e


getObjectAssertion :: XMLBase -> Element -> AS.Axiom
getObjectAssertion b e =
   let as = getAllAnnos b e
       op = getObjProp b $ filterCL objectPropList e
       [hd, lst] = map (getIRI b) $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" -> AS.Assertion $ AS.ObjectPropertyAssertion as op hd lst
    "NegativeObjectPropertyAssertion" ->
        AS.Assertion $ AS.NegativeObjectPropertyAssertion as op hd lst
    _ -> getIndividualAssertion b e

getIndividualAssertion :: XMLBase -> Element -> AS.Axiom
getIndividualAssertion b e =
   let as = getAllAnnos b e
       ind = map (getIRI b) $ filterChL individualList e
   in case getName e of
    "SameIndividual" -> AS.Assertion $ AS.SameIndividual as ind
    "DifferentIndividuals" -> AS.Assertion $ AS.DifferentIndividuals as ind
    _ -> getClassAssertion b e

getClassAssertion :: XMLBase -> Element -> AS.Axiom
getClassAssertion b e = case getName e of
    "ClassAssertion" ->
        let as = getAllAnnos b e
            ce = getClassExpression b $ filterCL classExpressionList e
            ind = getIRI b $ filterCL individualList e
        in AS.Assertion $ AS.ClassAssertion as ce ind
    _ -> getAnnoAxiom b e

getAnnoAxiom :: XMLBase -> Element -> AS.Axiom
getAnnoAxiom b e =
   let as = getAllAnnos b e
       ap = getIRI b $ filterC "AnnotationProperty" e
       [ch] = filterChL [iriK, abbreviatedIRI] e
       anIri = contentIRI b ch
    in case getName e of
    "AnnotationAssertion" ->
       let [s, v] = filterChL annotationValueList e
           sub = getSubject b s
        -- TODO: What about iris?
       in AS.AnnotationAxiom $ AS.AnnotationAssertion as ap (AS.AnnSubIri sub) (getValue b v)
       -- the misc will be converted to entities in static analysis
    --    in PlainAxiom (Misc [AS.Annotation [] sub $ AS.AnnValue sub])
    --        $ AnnFrameBit [AS.Annotation as ap (getValue b v)]
    --                 $ AnnotationFrameBit Assertion
    "SubAnnotationPropertyOf" ->
        let [hd, lst] = map (getIRI b) $ filterCh "AnnotationProperty" e
        in AS.AnnotationAxiom $ AS.SubAnnotationPropertyOf as hd lst
    "AnnotationPropertyDomain" -> AS.AnnotationAxiom $ AS.AnnotationPropertyDomain as ap anIri
    "AnnotationPropertyRange" -> AS.AnnotationAxiom $ AS.AnnotationPropertyRange as ap anIri
    -- TODO: How to handle such errors?
    -- _ -> PlainAxiom (Misc []) . AnnFrameBit [] . AnnotationFrameBit
    --   . XmlError $ getName e
    s -> err $ "Unexpected element '" ++ s ++ "'."

xmlErrorString :: Axiom -> Maybe String
xmlErrorString a = case a of
   PlainAxiom (Misc []) (AnnFrameBit [] (AnnotationFrameBit (XmlError e)))
     -> Just e
   _ -> Nothing


getOnlyAxioms :: XMLBase -> Element -> [AS.Axiom]
getOnlyAxioms b e = map (getDeclaration b) $ filterChildrenName isNotSmth e

getImports :: Map.Map String String -> XMLBase -> Element -> AS.DirectlyImportsDocuments
getImports m b e = map (importIRI m b) $ filterCh importK e

get1Map :: Element -> (String, String)
get1Map e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, pmap)

getPrefixMap :: Element -> GA.PrefixMap
getPrefixMap = AS.changePrefixMapTypeToGA . Map.fromList . map get1Map . filterCh "Prefix"

getOntologyIRI :: XMLBase -> Element -> Maybe IRI
getOntologyIRI b e =
  let oi = findAttr (unqual "ontologyIRI") e
  in fmap (\anIri -> appendBase b $ nullIRI {iriPath = stringToId anIri}) oi

getVersionIRI :: XMLBase -> Element -> Maybe IRI
getVersionIRI b e =
  let oi = findAttr (unqual "versionIRI") e
  in fmap (\anIri -> appendBase b $ nullIRI {iriPath = stringToId anIri}) oi

getBase :: Element -> XMLBase
getBase e = fromJust $ vFindAttrBy (isSmth "base") e

-- | parses an ontology document
xmlBasicSpec :: Map.Map String String -> Element -> AS.OntologyDocument
xmlBasicSpec imap e =
    let b = getBase e
        ax = getOnlyAxioms b e
        -- es = mapMaybe xmlErrorString ax
        -- em = Map.fromListWith (+) $ map (\ s -> (s, 1 :: Int)) es
    in
    -- (if Map.null em then id else
    --   trace ("ignored element tags: "
    --          ++ unwords (map (\ (s, c) ->
    --             if c > 1 then s ++ " (" ++ show c ++ " times)" else s)
    --                      $ Map.toList em)))
        AS.OntologyDocument
            (AS.OntologyMetadata AS.XML)
            (getPrefixMap e)
            $ AS.Ontology
                (getOntologyIRI b e)
                (getVersionIRI b e)
                (getImports imap b e)
                (getAllAnnos b e)
                ax
