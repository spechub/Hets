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
import Common.Id (stringToId, tokStr, getTokens)
import qualified Common.GlobalAnnotations as GA (PrefixMap)


import OWL2.AS
import OWL2.Keywords
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

getIRIWithType :: GA.PrefixMap -> XMLBase -> String -> String -> IRI
getIRIWithType pm b typ iriStr = expandIRI pm $ case typ of
        "abbreviatedIRI" ->  case parseCurie iriStr of
            Just i -> i
            Nothing -> error $ "could not get CURIE from " ++ show iriStr
        "IRI" -> let parsed = getIRIWithResolvedBase b iriStr in
            maybe (error $ "could not get IRI from " ++ show iriStr) id parsed
        "nodeID" -> case parseCurie iriStr of
            Just i -> i {isBlankNode = True}
            Nothing -> error $ "could not get nodeID from " ++ show iriStr
        "facet" -> let parsed = getIRIWithResolvedBase b iriStr in
            maybe (error $ "could not get facet from " ++ show iriStr) id parsed
        _ -> error $ "wrong qName:" ++ show typ

-- | parses an IRI
getIRI :: GA.PrefixMap -> XMLBase -> Element -> IRI
getIRI pm b e =
    let [a] = elAttribs e
        anIri = attrVal a
    in getIRIWithType pm b (qName $ attrKey a) anIri


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

-- | gets the content of an element with name IRI, AbbreviatedIRI or Import
contentIRI :: GA.PrefixMap -> XMLBase -> Element -> IRI
contentIRI pm b e = getIRIWithType pm b (getName e) (strContent e)

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

getEntity :: GA.PrefixMap -> XMLBase -> Element -> Entity
getEntity pm b e = mkEntity (getEntityType $ (qName . elName) e) $ getIRI pm b e

getDeclaration :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getDeclaration pm b e = case getName e of
   "Declaration" ->
       Declaration (getAllAnnos pm b e) (getEntity pm b $ filterCL entityList e)
   _ -> getClassAxiom pm b e

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

getLiteral :: GA.PrefixMap -> Element -> Literal
getLiteral pm e = case getName e of
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
                         else case parseIRIReference dt of
                            Just f -> correctLit $ Literal lf $ Typed (expandIRI pm f)
                            _ -> error $ "could not get datatypeIRI from " ++ show dt
    _ -> err "not literal"

getValue :: GA.PrefixMap -> XMLBase -> Element -> AnnotationValue
getValue pm b e = case getName e of
    "Literal" -> AnnValLit $ getLiteral pm e
    "AnonymousIndividual" -> AnnValue $ getIRI pm b e
    _ -> AnnValue $ contentIRI pm b e

getSubject :: GA.PrefixMap -> XMLBase -> Element -> IRI
getSubject pm b e = case getName e of
    "AnonymousIndividual" -> getIRI pm b e
    _ -> contentIRI pm b e

getAnnotation :: GA.PrefixMap -> XMLBase -> Element -> Annotation
getAnnotation pm b e =
     let hd = filterCh "Annotation" e
         [ap] = filterCh "AnnotationProperty" e
         av = filterCL annotationValueList e
     in Annotation (map (getAnnotation pm b) hd) (getIRI pm b ap) $ getValue pm b av

-- | returns a list of annotations
getAllAnnos :: GA.PrefixMap -> XMLBase -> Element -> [Annotation]
getAllAnnos pm b e = map (getAnnotation pm b) $ filterCh "Annotation" e

getObjProp :: GA.PrefixMap -> XMLBase -> Element -> ObjectPropertyExpression
getObjProp pm b e = case getName e of
  "ObjectProperty" -> ObjectProp $ getIRI pm b e
  "ObjectInverseOf" ->
    let [ch] = elChildren e
        [cch] = elChildren ch
    in case getName ch of
      "ObjectInverseOf" -> getObjProp pm b cch
      "ObjectProperty" -> ObjectInverseOf $ ObjectProp $ getIRI pm b ch
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

getFacetValuePair :: GA.PrefixMap -> XMLBase -> Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair pm b e = case getName e of
    "FacetRestriction" ->
       let [ch] = elChildren e
       in (properFacet $ getIRI pm b e, getLiteral pm ch)
    _ -> err "not facet"

getDataRange :: GA.PrefixMap -> XMLBase -> Element -> DataRange
getDataRange pm b e =
  let ch@(ch1 : _) = elChildren e
  in case getName e of
    "Datatype" -> DataType (getIRI pm b e) []
    "DatatypeRestriction" ->
        let dt = getIRI pm b $ filterC "Datatype" e
            fvp = map (getFacetValuePair pm b) $ filterCh "FacetRestriction" e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf $ getDataRange pm b ch1
    "DataOneOf" -> DataOneOf $ map (getLiteral pm) $ filterCh "Literal" e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map (getDataRange pm b) ch
    "DataUnionOf" -> DataJunction UnionOf $ map (getDataRange pm b) ch
    _ -> err "not data range"

getClassExpression :: GA.PrefixMap -> XMLBase -> Element -> ClassExpression
getClassExpression pm b e =
  let ch = elChildren e
      ch1 : _ = ch
      rch1 : _ = reverse ch
  in case getName e of
    "Class" -> Expression $ getIRI pm b e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map (getClassExpression pm b) ch
    "ObjectUnionOf" -> ObjectJunction UnionOf $ map (getClassExpression pm b) ch
    "ObjectComplementOf" -> ObjectComplementOf $ getClassExpression pm b ch1
    "ObjectOneOf" -> ObjectOneOf $ map (getIRI pm b) ch
    "ObjectSomeValuesFrom" -> ObjectValuesFrom SomeValuesFrom
            (getObjProp pm b ch1) $ getClassExpression pm b rch1
    "ObjectAllValuesFrom" -> ObjectValuesFrom AllValuesFrom
            (getObjProp pm b ch1) $ getClassExpression pm b rch1
    "ObjectHasValue" -> ObjectHasValue (getObjProp pm b ch1) $ getIRI pm b rch1
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp pm b ch1
    "DataSomeValuesFrom" -> DataValuesFrom SomeValuesFrom ([getIRI pm b ch1])
            $ getDataRange pm b rch1
    "DataAllValuesFrom" -> DataValuesFrom AllValuesFrom ([getIRI pm b ch1])
            $ getDataRange pm b rch1
    "DataHasValue" -> DataHasValue (getIRI pm b ch1) $ getLiteral pm rch1
    _ -> getObjCard pm b e ch rch1

getObjCard :: GA.PrefixMap -> XMLBase -> Element -> [Element] -> Element -> ClassExpression
getObjCard pm b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        op = getObjProp pm b ch1
        ce = if length ch == 2
                then Just $ getClassExpression pm b rch1
                else Nothing
    in case getName e of
        "ObjectMinCardinality" -> ObjectCardinality $ Cardinality
            MinCardinality i op ce
        "ObjectMaxCardinality" -> ObjectCardinality $ Cardinality
            MaxCardinality i op ce
        "ObjectExactCardinality" -> ObjectCardinality $ Cardinality
            ExactCardinality i op ce
        _ -> getDataCard pm b e ch rch1

getDataCard :: GA.PrefixMap -> XMLBase -> Element -> [Element] -> Element -> ClassExpression
getDataCard pm b e ch rch1 =
    let ch1 : _ = ch
        i = getInt e
        dp = getIRI pm b ch1
        dr = if length ch == 2
                then Just $ getDataRange pm b rch1
                else Nothing
    in case getName e of
        "DataMinCardinality" -> DataCardinality $ Cardinality
              MinCardinality i dp dr
        "DataMaxCardinality" -> DataCardinality $ Cardinality
              MaxCardinality i dp dr
        "DataExactCardinality" -> DataCardinality $ Cardinality
              ExactCardinality i dp dr
        _ -> err "not class expression"

getClassAxiom :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getClassAxiom pm b e =
   let ch = elChildren e
       as = getAllAnnos pm b e
       l@(hd : tl) = filterChL classExpressionList e
       [dhd, dtl] = filterChL dataRangeList e
       cel = map (getClassExpression pm b) l
   in case getName e of
    "SubClassOf" ->
       let [sub, super] = getClassExpression pm b <$> drop (length ch - 2) ch
       in ClassAxiom $ SubClassOf as sub super
    "EquivalentClasses" -> ClassAxiom $ EquivalentClasses as cel
    "DisjointClasses" -> ClassAxiom $ DisjointClasses as cel
    "DisjointUnion" -> case getClassExpression pm b hd of
        Expression c -> ClassAxiom $ DisjointUnion as c (getClassExpression pm b <$> tl)
        _ -> err "Invalid ClassExpression. DisjointUnion must have a class."
    "DatatypeDefinition" ->
        DatatypeDefinition as (getIRI pm b dhd) (getDataRange pm b dtl)
    _ -> getKey pm b e

getKey :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getKey pm b e = case getName e of
  "HasKey" ->
    let as = getAllAnnos pm b e
        [ce] = filterChL classExpressionList e
        op = map (getObjProp pm b) $ filterChL objectPropList e
        dp = map (getIRI pm b) $ filterChL dataPropList e
    in HasKey as (getClassExpression pm b ce) op dp
  _ -> getOPAxiom pm b e

getOPAxiom :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getOPAxiom pm b e =
   let as = getAllAnnos pm b e
       op = getObjProp pm b $ filterCL objectPropList e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map $ getObjProp pm b) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let [o1, o2] = map (getObjProp pm b) $ filterChL objectPropList e
                  in ObjectPropertyAxiom $ 
                    SubObjectPropertyOf as (SubObjPropExpr_obj o1) o2
             else ObjectPropertyAxiom $ 
                SubObjectPropertyOf as (SubObjPropExpr_exprchain opchain) op
    "EquivalentObjectProperties" ->
       let opl = map (getObjProp pm b) $ filterChL objectPropList e
       in ObjectPropertyAxiom $ 
        EquivalentObjectProperties as opl
    "DisjointObjectProperties" ->
       let opl = map (getObjProp pm b) $ filterChL objectPropList e
       in ObjectPropertyAxiom $ 
        DisjointObjectProperties as opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression pm b $ filterCL classExpressionList e
       in ObjectPropertyAxiom $ 
        ObjectPropertyDomain as op ce
    "ObjectPropertyRange" ->
       let ce = getClassExpression pm b $ filterCL classExpressionList e
       in ObjectPropertyAxiom $ 
        ObjectPropertyRange as op ce
    "InverseObjectProperties" ->
       let [hd, lst] = map (getObjProp pm b) $ filterChL objectPropList e
       in ObjectPropertyAxiom $ 
        InverseObjectProperties as hd lst
    "FunctionalObjectProperty" -> ObjectPropertyAxiom $ 
        FunctionalObjectProperty as op
    "InverseFunctionalObjectProperty" -> ObjectPropertyAxiom $ 
        InverseFunctionalObjectProperty as op
    "ReflexiveObjectProperty" -> ObjectPropertyAxiom $ 
        ReflexiveObjectProperty as op
    "IrreflexiveObjectProperty" -> ObjectPropertyAxiom $ 
        IrreflexiveObjectProperty as op
    "SymmetricObjectProperty" -> ObjectPropertyAxiom $ 
        SymmetricObjectProperty as op
    "AsymmetricObjectProperty" -> ObjectPropertyAxiom $ 
        AsymmetricObjectProperty as op
    "TransitiveObjectProperty" -> ObjectPropertyAxiom $ 
        TransitiveObjectProperty as op
    _ -> getDPAxiom pm b e

getDPAxiom :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getDPAxiom pm b e =
   let as = getAllAnnos pm b e
   in case getName e of
    "SubDataPropertyOf" ->
        let [hd, lst] = map (getIRI pm b) $ filterChL dataPropList e
        in DataPropertyAxiom $ SubDataPropertyOf as hd lst
    "EquivalentDataProperties" ->
        let dpl = map (getIRI pm b) $ filterChL dataPropList e
        in DataPropertyAxiom $ EquivalentDataProperties as dpl
    "DisjointDataProperties" ->
        let dpl = map (getIRI pm b) $ filterChL dataPropList e
        in DataPropertyAxiom $ DisjointDataProperties as dpl
    "DataPropertyDomain" ->
        let dp = getIRI pm b $ filterCL dataPropList e
            ce = getClassExpression pm b $ filterCL classExpressionList e
        in DataPropertyAxiom $ DataPropertyDomain as dp ce
    "DataPropertyRange" ->
        let dp = getIRI pm b $ filterCL dataPropList e
            dr = getDataRange pm b $ filterCL dataRangeList e
        in DataPropertyAxiom $ DataPropertyRange as dp dr
    "FunctionalDataProperty" ->
        let dp = getIRI pm b $ filterCL dataPropList e
        in DataPropertyAxiom $ FunctionalDataProperty as dp
    _ -> getDataAssertion pm b e

getDataAssertion :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getDataAssertion pm b e =
   let as = getAllAnnos pm b e
       dp = getIRI pm b $ filterCL dataPropList e
       ind = getIRI pm b $ filterCL individualList e
       lit = getLiteral pm $ filterC "Literal" e
   in case getName e of
    "DataPropertyAssertion" -> Assertion $ DataPropertyAssertion as dp ind lit
    "NegativeDataPropertyAssertion" -> 
        Assertion $  NegativeDataPropertyAssertion as dp ind lit
    _ -> getObjectAssertion pm b e


getObjectAssertion :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getObjectAssertion pm b e =
   let as = getAllAnnos pm b e
       op = getObjProp pm b $ filterCL objectPropList e
       [hd, lst] = map (getIRI pm b) $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" -> Assertion $ ObjectPropertyAssertion as op hd lst
    "NegativeObjectPropertyAssertion" ->
        Assertion $ NegativeObjectPropertyAssertion as op hd lst
    _ -> getIndividualAssertion pm b e

getIndividualAssertion :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getIndividualAssertion pm b e =
   let as = getAllAnnos pm b e
       ind = map (getIRI pm b) $ filterChL individualList e
   in case getName e of
    "SameIndividual" -> Assertion $ SameIndividual as ind
    "DifferentIndividuals" -> Assertion $ DifferentIndividuals as ind
    _ -> getClassAssertion pm b e

getClassAssertion :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getClassAssertion pm b e = case getName e of
    "ClassAssertion" ->
        let as = getAllAnnos pm b e
            ce = getClassExpression pm b $ filterCL classExpressionList e
            ind = getIRI pm b $ filterCL individualList e
        in Assertion $ ClassAssertion as ce ind
    _ -> getAnnoAxiom pm b e

getAnnoAxiom :: GA.PrefixMap -> XMLBase -> Element -> Axiom
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
       in AnnotationAxiom $ AnnotationAssertion as ap (AnnSubIri sub) (getValue pm b v)
       -- the misc will be converted to entities in static analysis
    --    in PlainAxiom (Misc [Annotation [] sub $ AnnValue sub])
    --        $ AnnFrameBit [Annotation as ap (getValue b v)]
    --                 $ AnnotationFrameBit Assertion
    "SubAnnotationPropertyOf" ->
        let [hd, lst] = map (getIRI pm b) $ filterCh "AnnotationProperty" e
        in AnnotationAxiom $ SubAnnotationPropertyOf as hd lst
    "AnnotationPropertyDomain" -> AnnotationAxiom $ AnnotationPropertyDomain as ap anIri
    "AnnotationPropertyRange" -> AnnotationAxiom $ AnnotationPropertyRange as ap anIri
    _ -> getRuleAxiom pm b e

getIArg :: GA.PrefixMap -> XMLBase -> Element -> IndividualArg
getIArg pm b e = case getName e of
    "Variable" -> IVar $ getIRI pm b e
    "NamedIndividual" -> IArg $ getIRI pm b e
    _ ->  err $ "Unexpected element '" ++ getName e ++ "'."

getDArg :: GA.PrefixMap -> XMLBase -> Element -> DataArg
getDArg pm b e = case getName e of
    "Variable" -> DVar $ getIRI pm b e
    "Literal" -> DArg $ getLiteral pm e
    _ ->  err $ "Unexpected element '" ++ getName e ++ "'."

getAtom :: GA.PrefixMap -> XMLBase -> Element -> Atom
getAtom pm b e =  case getName e of
    "ClassAtom" ->
        let [clExpr, iarg] = elChildren e
        in ClassAtom (getClassExpression pm b clExpr) (getIArg pm b iarg)
    "DataRangeAtom" ->
        let [dr, darg] = elChildren e
        in DataRangeAtom (getDataRange pm b dr) (getDArg pm b darg)
    "ObjectPropertyAtom" ->
        let [obExpr, iarg1, iarg2] = elChildren e
        in ObjectPropertyAtom
            (getObjProp pm b obExpr)
            (getIArg pm b iarg1)
            (getIArg pm b iarg2)
    "DataPropertyAtom" ->
        let [dpExp, iarg, darg] = elChildren e
        in DataPropertyAtom
            (getIRI pm b dpExp)
            (getIArg pm b iarg)
            (getDArg pm b darg)
    "BuiltInAtom" ->
        let dargs = getDArg pm b <$> elChildren e
        in BuiltInAtom (getIRI pm b e) dargs
    "SameIndividualAtom" ->
        let [iarg1, iarg2] = getIArg pm b <$> elChildren e
        in SameIndividualAtom iarg1 iarg2
    "DifferentIndividualsAtom" ->
        let [iarg1, iarg2] = getIArg pm b <$> elChildren e
        in DifferentIndividualsAtom iarg1 iarg2
    _ ->  err $ "Unexpected element '" ++ getName e ++ "'."
    


getRuleAxiom :: GA.PrefixMap -> XMLBase -> Element -> Axiom
getRuleAxiom pm b e = case getName e of
    "DLSafeRule" ->
        let as = getAllAnnos pm b e
            atoms = elChildren . (`filterC` e)
            bd = getAtom pm b <$> atoms "Body"
            hd = getAtom pm b <$> atoms "Head"
        in Rule $ DLSafeRule as bd hd
    s -> err $ "Unexpected element '" ++ s ++ "'."


getOnlyAxioms :: GA.PrefixMap -> XMLBase -> Element -> [Axiom]
getOnlyAxioms pm b e = map (getDeclaration pm b) $ filterChildrenName isNotSmth e

getImports :: GA.PrefixMap -> XMLBase -> Element -> DirectlyImportsDocuments
getImports m b e = map (contentIRI m b) $ filterCh importK e

get1Map :: Element -> (String, String)
get1Map e =
  let [pref, pmap] = map attrVal $ elAttribs e
  in (pref, pmap)

getPrefixMap :: Element -> GA.PrefixMap
getPrefixMap e = changePrefixMapTypeToGA $ Map.map (\x -> "<" ++ x ++ ">") $ Map.fromList $ map get1Map $ filterCh "Prefix" e

getOntologyIRI :: XMLBase -> Element -> Maybe IRI
getOntologyIRI b e =
  let oi = findAttr (unqual "ontologyIRI") e
  in oi >>= getIRIWithResolvedBase b

getVersionIRI :: XMLBase -> Element -> Maybe IRI
getVersionIRI b e =
  let vi = findAttr (unqual "versionIRI") e
  in vi >>= getIRIWithResolvedBase b

getBase :: Element -> XMLBase
getBase e = vFindAttrBy (isSmth "base") e

-- | parses an ontology document
xmlBasicSpec :: Map.Map String String -> Element -> OntologyDocument
xmlBasicSpec imap e =
    let b = getBase e
        pm = changePrefixMapTypeToGA imap `Map.union` getPrefixMap e
        ax = getOnlyAxioms pm b e
    in
        OntologyDocument
            (OntologyMetadata XML)
            pm
            $ Ontology
                (getOntologyIRI b e)
                (getVersionIRI b e)
                (getImports pm b e)
                (getAllAnnos pm b e)
                ax
