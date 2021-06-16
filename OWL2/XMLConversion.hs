{- |
Module      :  ./OWL2/XMLConversion.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Conversion from Manchester Syntax to XML Syntax
-}

module OWL2.XMLConversion where

import Common.AS_Annotation (Named, sentence)
import Common.IRI hiding (showIRI)
import Common.Id

import qualified OWL2.AS as AS
import OWL2.MS
import OWL2.Sign
import OWL2.XML
import OWL2.XMLKeywords

import Text.XML.Light

import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- | prints the IRI with a colon separating the prefix and the local part
showIRI :: IRI -> String
showIRI iri = prefixName iri ++ show (iriPath iri)

nullQN :: Text.XML.Light.QName
nullQN = QName "" Nothing Nothing

nullElem :: Element
nullElem = Element nullQN [] [] Nothing

makeQN :: String -> Text.XML.Light.QName
makeQN s = nullQN {qName = s}

-- | sets the content of an element to a list of given elements
setContent :: [Element] -> Element -> Element
setContent cl e = e {elContent = map Elem cl}

-- | sets the content of an element to a given string
setText :: String -> Element -> Element
setText s e = e {elContent = [Text CData {cdVerbatim = CDataText,
    cdData = s, cdLine = Nothing}]}

setQNPrefix :: String -> Text.XML.Light.QName -> Text.XML.Light.QName
setQNPrefix s qn = qn {qPrefix = Just s}

{- | sets the name of an element to a given string
 and the namespace to <http://www.w3.org/2002/07/owl#> -}
setName :: String -> Element -> Element
setName s e = e {elName = nullQN {qName = s,
    qURI = Just "http://www.w3.org/2002/07/owl#"} }

{- | sets the attribute key to one of IRI, abbreviatedIRI or nodeID
 and the attribute value to the actual content of the IRI -}
setIRI :: IRI -> Element -> Element
setIRI iri e =
    let ty
            | hasFullIRI iri = iriK
            | isBlankNode iri = nodeID
            | otherwise = "abbreviatedIRI"
    in e {elAttribs = [Attr {attrKey = makeQN ty,
                             attrVal = showIRI $ AS.setReservedPrefix iri}]}

mwIRI :: IRI -> Element
mwIRI iri = setIRI iri nullElem

-- | makes an element with the string as name and the IRI as content
mwNameIRI :: String -> IRI -> Element
mwNameIRI s iri = setName s $ mwIRI iri

-- | makes a new element with the given string as name
mwString :: String -> Element
mwString s = setName s nullElem

-- | makes a new element with the string as name and an element as content
makeElementWith1 :: String -> Element -> Element
makeElementWith1 s e = setContent [e] $ mwString s

{- | makes a new element with the string as name and the list of elements
    as content -}
makeElement :: String -> [Element] -> Element
makeElement s el = setContent el $ mwString s

mwText :: String -> Element
mwText s = setText s nullElem

-- | makes a new element with the IRI as the text content
mwSimpleIRI :: IRI -> Element
mwSimpleIRI s = setName (if hasFullIRI s then iriK
                          else abbreviatedIRI) $ mwText $ showIRI
                          $ AS.setReservedPrefix s

{- | generates a list of elements, all with the first string as name,
    and each with the content in this order: first, the list of elements
    in the given pair (usually annotations) and second, the result of the
    application of the function (given as fourth argument) on the second string
    and the given IRI -}
make1 :: Bool -> String -> String -> (String -> IRI -> Element) -> IRI ->
            [([Element], Element)] -> [Element]
make1 rl hdr shdr f iri = map (\ (a, b) -> makeElement hdr
        $ a ++ (if rl then [f shdr iri, b] else [b, f shdr iri]))

-- almost the same, just that the function takes only one argument
make2 :: Bool -> String -> (a -> Element) -> a ->
            [([Element], Element)] -> [Element]
make2 rl hdr f expr = map (\ (x, y) -> makeElement hdr
        $ x ++ (if rl then [f expr, y] else [y, f expr]))

-- | sets the cardinality
setInt :: Int -> Element -> Element
setInt i e = e {elAttribs = [Attr {attrKey = makeQN "cardinality",
    attrVal = show i}]}

-- | the reverse of @properFacet@ in "OWL2.XML"
correctFacet :: AS.ConstrainingFacet -> AS.ConstrainingFacet
correctFacet c = let d = AS.getPredefName c in setPrefix "http" $ mkIRI $
    "//www.w3.org/2001/XMLSchema#" ++ case d of
        ">" -> "minExclusive"
        "<" -> "maxExclusive"
        ">=" -> "minInclusive"
        "<=" -> "maxInclusive"
        _ -> d

-- | sets either a literal datatype or a facet
setDt :: Bool -> IRI -> Element -> Element
setDt b dt e = e {elAttribs = elAttribs e ++ [Attr {attrKey
    = makeQN (if b then "datatypeIRI" else "facet"),
      attrVal = showIRI $ if b then AS.setReservedPrefix dt else correctFacet dt}]}

setLangTag :: Maybe AS.LanguageTag -> Element -> Element
setLangTag ml e = case ml of
    Nothing -> e
    Just lt -> e {elAttribs = elAttribs e ++ [Attr {attrKey
        = setQNPrefix "xml" (makeQN "lang"), attrVal = lt}]}

xmlEntity :: AS.Entity -> Element
xmlEntity (AS.Entity _ ty ent) = mwNameIRI (case ty of
    AS.Class -> classK
    AS.Datatype -> datatypeK
    AS.ObjectProperty -> objectPropertyK
    AS.DataProperty -> dataPropertyK
    AS.AnnotationProperty -> annotationPropertyK
    AS.NamedIndividual -> namedIndividualK) ent

xmlLiteral :: AS.Literal -> Element
xmlLiteral l = case l of
  AS.Literal lf tu ->
    let part = setName literalK $ mwText lf
    in case tu of
        AS.Typed dt -> setDt True dt part
        AS.Untyped lang -> setLangTag lang $ setDt True (splitIRI $ mkIRI
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
            part
  AS.NumberLit f -> setDt True (nullIRI {iriScheme = "http:",
        iriPath = stringToId $ "//www.w3.org/2001/XMLSchema#" ++ AS.numberName f})
        $ setName literalK $ mwText $ show f

xmlIndividual :: IRI -> Element
xmlIndividual iri =
    mwNameIRI (if AS.isAnonymous iri then anonymousIndividualK
                else namedIndividualK) iri

xmlFVPair :: (AS.ConstrainingFacet, AS.RestrictionValue) -> Element
xmlFVPair (cf, rv) = setDt False cf $ makeElement facetRestrictionK
    [xmlLiteral rv]

xmlObjProp :: AS.ObjectPropertyExpression -> Element
xmlObjProp ope = case ope of
    AS.ObjectProp op -> mwNameIRI objectPropertyK op
    AS.ObjectInverseOf i -> makeElement objectInverseOfK [xmlObjProp i]

xmlDataRange :: AS.DataRange -> Element
xmlDataRange dr = case dr of
    AS.DataType dt cfl ->
        let dtelem = mwNameIRI datatypeK dt
        in if null cfl then dtelem
            else makeElement datatypeRestrictionK
            $ dtelem : map xmlFVPair cfl
    AS.DataJunction jt drl -> makeElement (
        case jt of
            AS.IntersectionOf -> dataIntersectionOfK
            AS.UnionOf -> dataUnionOfK)
        $ map xmlDataRange drl
    AS.DataComplementOf drn -> makeElement dataComplementOfK
        [xmlDataRange drn]
    AS.DataOneOf ll -> makeElement dataOneOfK
        $ map xmlLiteral ll

xmlClassExpression :: AS.ClassExpression -> Element
xmlClassExpression ce = case ce of
    AS.Expression c -> mwNameIRI classK c
    AS.ObjectJunction jt cel -> makeElement (
        case jt of
            AS.IntersectionOf -> objectIntersectionOfK
            AS.UnionOf -> objectUnionOfK)
        $ map xmlClassExpression cel
    AS.ObjectComplementOf cex -> makeElement objectComplementOfK
        [xmlClassExpression cex]
    AS.ObjectOneOf il -> makeElement objectOneOfK
        $ map xmlIndividual il
    AS.ObjectValuesFrom qt ope cex -> makeElement (
        case qt of
            AS.AllValuesFrom -> objectAllValuesFromK
            AS.SomeValuesFrom -> objectSomeValuesFromK)
        [xmlObjProp ope, xmlClassExpression cex]
    AS.ObjectHasValue ope i -> makeElement objectHasValueK
        [xmlObjProp ope, xmlIndividual i]
    AS.ObjectHasSelf ope -> makeElement objectHasSelfK [xmlObjProp ope]
    AS.ObjectCardinality (AS.Cardinality ct i op mce) -> setInt i $ makeElement (
        case ct of
            AS.MinCardinality -> objectMinCardinalityK
            AS.MaxCardinality -> objectMaxCardinalityK
            AS.ExactCardinality -> objectExactCardinalityK)
        $ xmlObjProp op :
        case mce of
            Nothing -> []
            Just cexp -> [xmlClassExpression cexp]
    AS.DataValuesFrom qt dp dr -> makeElement (
        case qt of
            AS.AllValuesFrom -> dataAllValuesFromK
            AS.SomeValuesFrom -> dataSomeValuesFromK)
        [mwNameIRI dataPropertyK (head dp), xmlDataRange dr]
    AS.DataHasValue dp l -> makeElement dataHasValueK
        [mwNameIRI dataPropertyK dp, xmlLiteral l]
    AS.DataCardinality (AS.Cardinality ct i dp mdr) -> setInt i $ makeElement (
        case ct of
            AS.MinCardinality -> dataMinCardinalityK
            AS.MaxCardinality -> dataMaxCardinalityK
            AS.ExactCardinality -> dataExactCardinalityK)
        $ mwNameIRI dataPropertyK dp :
            case mdr of
                Nothing -> []
                Just dr -> [xmlDataRange dr]

xmlAnnotation :: AS.Annotation -> Element
xmlAnnotation (AS.Annotation al ap av) = makeElement annotationK
    $ map xmlAnnotation al ++ [mwNameIRI annotationPropertyK ap,
    case av of
        AS.AnnValue iri -> xmlSubject iri
        AS.AnnValLit l -> xmlLiteral l]

xmlSubject :: IRI -> Element
xmlSubject iri = if AS.isAnonymous iri then xmlIndividual iri
                  else mwSimpleIRI iri

xmlAnnotations :: Annotations -> [Element]
xmlAnnotations = map xmlAnnotation

xmlAL :: (a -> Element) -> AnnotatedList a -> [([Element], Element)]
xmlAL f al = let annos = map (xmlAnnotations . fst) al
                 other = map (\ (_, b) -> f b) al
             in zip annos other

xmlLFB :: Extended -> Maybe AS.Relation -> ListFrameBit -> [Element]
xmlLFB ext mr lfb = case lfb of
    AnnotationBit al ->
        let list = xmlAL mwSimpleIRI al
            SimpleEntity (AS.Entity _ _ ap) = ext
        in case fromMaybe (error "expected domain, range, subproperty") mr of
            AS.SubPropertyOf ->
                let list2 = xmlAL (mwNameIRI annotationPropertyK) al
                in make1 True subAnnotationPropertyOfK annotationPropertyK
                         mwNameIRI ap list2
            AS.DRRelation AS.ADomain -> make1 True annotationPropertyDomainK
                        annotationPropertyK mwNameIRI ap list
            AS.DRRelation AS.ARange -> make1 True annotationPropertyRangeK
                        annotationPropertyK mwNameIRI ap list
            _ -> error "bad annotation bit"
    ExpressionBit al ->
        let list = xmlAL xmlClassExpression al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint--, class") mr of
                    AS.EDRelation AS.Equivalent -> equivalentClassesK
                    AS.EDRelation AS.Disjoint -> disjointClassesK
                    _ -> error "bad equiv or disjoint classes bit"
                ) $ xmlAnnotations anno ++ map snd list]
            ClassEntity c -> make2 True (case fromMaybe
                (error "expected equiv--, disjoint--, sub-- class") mr of
                    AS.SubClass -> subClassOfK
                    AS.EDRelation AS.Equivalent -> equivalentClassesK
                    AS.EDRelation AS.Disjoint -> disjointClassesK
                    _ -> error "bad equiv, disjoint, subClass bit")
                xmlClassExpression c list
            ObjectEntity op -> make2 True (case fromMaybe
                (error "expected domain, range") mr of
                    AS.DRRelation AS.ADomain -> objectPropertyDomainK
                    AS.DRRelation AS.ARange -> objectPropertyRangeK
                    _ -> "bad object domain or range bit") xmlObjProp op list
            SimpleEntity (AS.Entity _ ty ent) -> case ty of
                AS.DataProperty -> make1 True dataPropertyDomainK dataPropertyK
                        mwNameIRI ent list
                AS.NamedIndividual -> make2 False classAssertionK
                        xmlIndividual ent list
                _ -> error "bad expression bit"
    ObjectBit al ->
        let list = xmlAL xmlObjProp al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- obj prop") mr of
                    AS.EDRelation AS.Equivalent -> equivalentObjectPropertiesK
                    AS.EDRelation AS.Disjoint -> disjointObjectPropertiesK
                    _ -> error "bad object bit (equiv, disjoint)"
                ) $ xmlAnnotations anno ++ map snd list]
            ObjectEntity o -> make2 True (case fromMaybe
                (error "expected sub, Inverse, equiv, disjoint op") mr of
                    AS.SubPropertyOf -> subObjectPropertyOfK
                    AS.InverseOf -> inverseObjectPropertiesK
                    AS.EDRelation AS.Equivalent -> equivalentObjectPropertiesK
                    AS.EDRelation AS.Disjoint -> disjointObjectPropertiesK
                    _ -> error "bad object bit (subpropertyof, inverseof)"
                ) xmlObjProp o list
            _ -> error "bad object bit"
    DataBit al ->
        let list = xmlAL (mwNameIRI dataPropertyK) al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- data prop") mr of
                    AS.EDRelation AS.Equivalent -> equivalentDataPropertiesK
                    AS.EDRelation AS.Disjoint -> disjointDataPropertiesK
                    _ -> error "bad data bit"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (AS.Entity _ _ ent) -> make1 True (case fromMaybe
                    (error "expected sub, equiv or disjoint data") mr of
                        AS.SubPropertyOf -> subDataPropertyOfK
                        AS.EDRelation AS.Equivalent -> equivalentDataPropertiesK
                        AS.EDRelation AS.Disjoint -> disjointDataPropertiesK
                        _ -> error "bad data bit"
                    ) dataPropertyK mwNameIRI ent list
            _ -> error "bad data bit"
    IndividualSameOrDifferent al ->
        let list = xmlAL xmlIndividual al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    AS.SDRelation AS.Same -> sameIndividualK
                    AS.SDRelation AS.Different -> differentIndividualsK
                    _ -> error "bad individual bit (s or d)"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (AS.Entity _ _ i) -> make2 True (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    AS.SDRelation AS.Same -> sameIndividualK
                    AS.SDRelation AS.Different -> differentIndividualsK
                    _ -> error "bad individual bit (s or d)"
                ) xmlIndividual i list
            _ -> error "bad individual same or different"
    ObjectCharacteristics al ->
        let ObjectEntity op = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, y) -> makeElement (case y of
                AS.Functional -> functionalObjectPropertyK
                AS.InverseFunctional -> inverseFunctionalObjectPropertyK
                AS.Reflexive -> reflexiveObjectPropertyK
                AS.Irreflexive -> irreflexiveObjectPropertyK
                AS.Symmetric -> symmetricObjectPropertyK
                AS.Asymmetric -> asymmetricObjectPropertyK
                AS.Transitive -> transitiveObjectPropertyK
                AS.Antisymmetric -> antisymmetricObjectPropertyK
            ) $ x ++ [xmlObjProp op]) list
    DataPropRange al ->
        let SimpleEntity (AS.Entity _ AS.DataProperty dp) = ext
            list = xmlAL xmlDataRange al
        in make1 True dataPropertyRangeK dataPropertyK mwNameIRI dp list
    IndividualFacts al ->
        let SimpleEntity (AS.Entity _ AS.NamedIndividual i) = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, f) -> case f of
            ObjectPropertyFact pn op ind ->
               makeElement (case pn of
                    AS.Positive -> objectPropertyAssertionK
                    AS.Negative -> negativeObjectPropertyAssertionK
                ) $ x ++ [xmlObjProp op] ++ map xmlIndividual [i, ind]
            DataPropertyFact pn dp lit ->
                makeElement (case pn of
                    AS.Positive -> dataPropertyAssertionK
                    AS.Negative -> negativeDataPropertyAssertionK
                ) $ x ++ [mwNameIRI dataPropertyK dp] ++
                        [xmlIndividual i] ++ [xmlLiteral lit]
            ) list

xmlAssertion :: IRI -> Annotations -> [Element]
xmlAssertion iri = map (\ (AS.Annotation as ap av) ->
    makeElement annotationAssertionK $ xmlAnnotations as
        ++ [mwNameIRI annotationPropertyK ap]
        ++ [xmlSubject iri, case av of
                AS.AnnValue avalue -> xmlSubject avalue
                AS.AnnValLit l -> xmlLiteral l])

xmlAFB :: Extended -> Annotations -> AnnFrameBit -> [Element]
xmlAFB ext anno afb = case afb of
    AnnotationFrameBit ty -> case ext of
        SimpleEntity ent -> case ty of
            Declaration -> [makeElement declarationK
                    $ xmlAnnotations anno ++ [xmlEntity ent]]
            Assertion -> if null anno then [makeElement declarationK
                                                [xmlEntity ent]]
                          else
                           let AS.Entity _ _ iri = ent in xmlAssertion iri anno
            XmlError _ -> error "xmlAFB"
        Misc ans -> let [AS.Annotation _ iri _] = ans in xmlAssertion iri anno
        ClassEntity ent -> case ent of
            AS.Expression c -> [makeElement declarationK
                    $ xmlAnnotations anno ++ [xmlEntity $ AS.mkEntity AS.Class c]]
            _ -> [] -- very rare cases
        ObjectEntity ent -> case ent of
            AS.ObjectProp o -> [makeElement declarationK
                    $ xmlAnnotations anno ++
                    [xmlEntity $ AS.mkEntity AS.ObjectProperty o]]
            _ -> [] -- very rare cases
    DataFunctional ->
        let SimpleEntity (AS.Entity _ _ dp) = ext
        in [makeElement functionalDataPropertyK
            $ xmlAnnotations anno ++ [mwNameIRI dataPropertyK dp]]
    DatatypeBit dr ->
        let SimpleEntity (AS.Entity _ _ dt) = ext
        in [makeElement datatypeDefinitionK
                $ xmlAnnotations anno ++ [mwNameIRI datatypeK dt,
                    xmlDataRange dr]]
    ClassDisjointUnion cel ->
        let ClassEntity c = ext
        in [makeElement disjointUnionK
                $ xmlAnnotations anno ++ map xmlClassExpression (c : cel)]
    ClassHasKey op dp ->
        let ClassEntity c = ext
        in [makeElement hasKeyK
                $ xmlAnnotations anno ++ [xmlClassExpression c]
                    ++ map xmlObjProp op ++ map (mwNameIRI dataPropertyK) dp]
    ObjectSubPropertyChain opl ->
        let ObjectEntity op = ext
            xmlop = map xmlObjProp opl
        in [makeElement subObjectPropertyOfK
                $ xmlAnnotations anno ++
                    [makeElement objectPropertyChainK xmlop, xmlObjProp op]]

xmlFrameBit :: Extended -> FrameBit -> [Element]
xmlFrameBit ext fb = case fb of
    ListFrameBit mr lfb -> xmlLFB ext mr lfb
    AnnFrameBit anno afb -> xmlAFB ext anno afb

xmlAxioms :: Axiom -> [Element]
xmlAxioms (PlainAxiom ext fb) = xmlFrameBit ext fb

xmlFrames :: Frame -> [Element]
xmlFrames (Frame ext fbl) = concatMap (xmlFrameBit ext) fbl

mkElemeDecl :: Sign -> String -> (Sign -> Set.Set IRI) -> [Element]
mkElemeDecl s k f = map (makeElementWith1 declarationK . mwNameIRI k)
    $ Set.toList $ f s

-- | converts the signature to declarations
signToDec :: Sign -> [Element]
signToDec s = concatMap (uncurry $ mkElemeDecl s)
    [ (classK, concepts)
    , (objectPropertyK, objectProperties)
    , (dataPropertyK, dataProperties)
    , (annotationPropertyK, annotationRoles)
    , (datatypeK, datatypes)
    , (namedIndividualK, individuals)]

xmlImport :: AS.ImportIRI -> Element
xmlImport i = setName importK $ mwText $ showIRI i

setPref :: String -> Element -> Element
setPref s e = e {elAttribs = Attr {attrKey = makeQN "name"
    , attrVal = s} : elAttribs e}

set1Map :: (String, String) -> Element
set1Map (s, iri) = setPref s $ mwIRI $ splitIRI $ mkIRI iri

xmlPrefixes :: AS.PrefixMap -> [Element]
xmlPrefixes pm = let allpm = Map.union pm AS.predefPrefixes in
    map (setName prefixK . set1Map) $ Map.toList allpm

setOntIRI :: AS.OntologyIRI -> Element -> Element
setOntIRI iri e =
    if elem iri [nullIRI, dummyIRI] then e
     else e {elAttribs = Attr {attrKey = makeQN "ontologyIRI",
        attrVal = showIRI iri} : elAttribs e}

setBase :: String -> Element -> Element
setBase s e = e {elAttribs = Attr {attrKey = nullQN {qName = "base",
        qPrefix = Just "xml"}, attrVal = s} : elAttribs e}

setXMLNS :: Element -> Element
setXMLNS e = e {elAttribs = Attr {attrKey = makeQN "xmlns", attrVal =
        "http://www.w3.org/2002/07/owl#"} : elAttribs e}

xmlOntologyDoc :: Sign -> OntologyDocument -> Element
xmlOntologyDoc s od =
    let ont = ontology od
        pd = prefixDeclaration od
        emptyPref = fromMaybe (showIRI dummyIRI) $ Map.lookup "" pd
    in setBase emptyPref $ setXMLNS $ setOntIRI (name ont)
        $ makeElement "Ontology" $ xmlPrefixes pd
            ++ map xmlImport (imports ont)
            ++ concatMap xmlFrames (ontFrames ont)
            ++ concatMap xmlAnnotations (ann ont)
            ++ signToDec s

mkODoc :: Sign -> [Named Axiom] -> String
mkODoc s = ppTopElement . xmlOntologyDoc s . OntologyDocument (prefixMap s)
  . emptyOntology . map (axToFrame . sentence)
