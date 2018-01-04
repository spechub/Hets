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

import OWL2.AS
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
                             attrVal = showIRI $ setReservedPrefix iri}]}

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
                          $ setReservedPrefix s

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
correctFacet :: ConstrainingFacet -> ConstrainingFacet
correctFacet c = let d = getPredefName c in setPrefix "http" $ mkIRI $
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
      attrVal = showIRI $ if b then setReservedPrefix dt else correctFacet dt}]}

setLangTag :: Maybe LanguageTag -> Element -> Element
setLangTag ml e = case ml of
    Nothing -> e
    Just lt -> e {elAttribs = elAttribs e ++ [Attr {attrKey
        = setQNPrefix "xml" (makeQN "lang"), attrVal = lt}]}

xmlEntity :: Entity -> Element
xmlEntity (Entity _ ty ent) = mwNameIRI (case ty of
    Class -> classK
    Datatype -> datatypeK
    ObjectProperty -> objectPropertyK
    DataProperty -> dataPropertyK
    AnnotationProperty -> annotationPropertyK
    NamedIndividual -> namedIndividualK) ent

xmlLiteral :: Literal -> Element
xmlLiteral l = case l of
  Literal lf tu ->
    let part = setName literalK $ mwText lf
    in case tu of
        Typed dt -> setDt True dt part
        Untyped lang -> setLangTag lang $ setDt True (splitIRI $ mkIRI
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
            part
  NumberLit f -> setDt True (nullIRI {iriScheme = "http",
        iriPath = stringToId $ "//www.w3.org/2001/XMLSchema#" ++ numberName f})
        $ setName literalK $ mwText $ show f

xmlIndividual :: IRI -> Element
xmlIndividual iri =
    mwNameIRI (if isAnonymous iri then anonymousIndividualK
                else namedIndividualK) iri

xmlFVPair :: (ConstrainingFacet, RestrictionValue) -> Element
xmlFVPair (cf, rv) = setDt False cf $ makeElement facetRestrictionK
    [xmlLiteral rv]

xmlObjProp :: ObjectPropertyExpression -> Element
xmlObjProp ope = case ope of
    ObjectProp op -> mwNameIRI objectPropertyK op
    ObjectInverseOf i -> makeElement objectInverseOfK [xmlObjProp i]

xmlDataRange :: DataRange -> Element
xmlDataRange dr = case dr of
    DataType dt cfl ->
        let dtelem = mwNameIRI datatypeK dt
        in if null cfl then dtelem
            else makeElement datatypeRestrictionK
            $ dtelem : map xmlFVPair cfl
    DataJunction jt drl -> makeElement (
        case jt of
            IntersectionOf -> dataIntersectionOfK
            UnionOf -> dataUnionOfK)
        $ map xmlDataRange drl
    DataComplementOf drn -> makeElement dataComplementOfK
        [xmlDataRange drn]
    DataOneOf ll -> makeElement dataOneOfK
        $ map xmlLiteral ll

xmlClassExpression :: ClassExpression -> Element
xmlClassExpression ce = case ce of
    Expression c -> mwNameIRI classK c
    ObjectJunction jt cel -> makeElement (
        case jt of
            IntersectionOf -> objectIntersectionOfK
            UnionOf -> objectUnionOfK)
        $ map xmlClassExpression cel
    ObjectComplementOf cex -> makeElement objectComplementOfK
        [xmlClassExpression cex]
    ObjectOneOf il -> makeElement objectOneOfK
        $ map xmlIndividual il
    ObjectValuesFrom qt ope cex -> makeElement (
        case qt of
            AllValuesFrom -> objectAllValuesFromK
            SomeValuesFrom -> objectSomeValuesFromK)
        [xmlObjProp ope, xmlClassExpression cex]
    ObjectHasValue ope i -> makeElement objectHasValueK
        [xmlObjProp ope, xmlIndividual i]
    ObjectHasSelf ope -> makeElement objectHasSelfK [xmlObjProp ope]
    ObjectCardinality (Cardinality ct i op mce) -> setInt i $ makeElement (
        case ct of
            MinCardinality -> objectMinCardinalityK
            MaxCardinality -> objectMaxCardinalityK
            ExactCardinality -> objectExactCardinalityK)
        $ xmlObjProp op :
        case mce of
            Nothing -> []
            Just cexp -> [xmlClassExpression cexp]
    DataValuesFrom qt dp dr -> makeElement (
        case qt of
            AllValuesFrom -> dataAllValuesFromK
            SomeValuesFrom -> dataSomeValuesFromK)
        [mwNameIRI dataPropertyK dp, xmlDataRange dr]
    DataHasValue dp l -> makeElement dataHasValueK
        [mwNameIRI dataPropertyK dp, xmlLiteral l]
    DataCardinality (Cardinality ct i dp mdr) -> setInt i $ makeElement (
        case ct of
            MinCardinality -> dataMinCardinalityK
            MaxCardinality -> dataMaxCardinalityK
            ExactCardinality -> dataExactCardinalityK)
        $ mwNameIRI dataPropertyK dp :
            case mdr of
                Nothing -> []
                Just dr -> [xmlDataRange dr]

xmlAnnotation :: Annotation -> Element
xmlAnnotation (Annotation al ap av) = makeElement annotationK
    $ map xmlAnnotation al ++ [mwNameIRI annotationPropertyK ap,
    case av of
        AnnValue iri -> xmlSubject iri
        AnnValLit l -> xmlLiteral l]

xmlSubject :: IRI -> Element
xmlSubject iri = if isAnonymous iri then xmlIndividual iri
                  else mwSimpleIRI iri

xmlAnnotations :: Annotations -> [Element]
xmlAnnotations = map xmlAnnotation

xmlAL :: (a -> Element) -> AnnotatedList a -> [([Element], Element)]
xmlAL f al = let annos = map (xmlAnnotations . fst) al
                 other = map (\ (_, b) -> f b) al
             in zip annos other

xmlLFB :: Extended -> Maybe Relation -> ListFrameBit -> [Element]
xmlLFB ext mr lfb = case lfb of
    AnnotationBit al ->
        let list = xmlAL mwSimpleIRI al
            SimpleEntity (Entity _ _ ap) = ext
        in case fromMaybe (error "expected domain, range, subproperty") mr of
            SubPropertyOf ->
                let list2 = xmlAL (mwNameIRI annotationPropertyK) al
                in make1 True subAnnotationPropertyOfK annotationPropertyK
                         mwNameIRI ap list2
            DRRelation ADomain -> make1 True annotationPropertyDomainK
                        annotationPropertyK mwNameIRI ap list
            DRRelation ARange -> make1 True annotationPropertyRangeK
                        annotationPropertyK mwNameIRI ap list
            _ -> error "bad annotation bit"
    ExpressionBit al ->
        let list = xmlAL xmlClassExpression al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint--, class") mr of
                    EDRelation Equivalent -> equivalentClassesK
                    EDRelation Disjoint -> disjointClassesK
                    _ -> error "bad equiv or disjoint classes bit"
                ) $ xmlAnnotations anno ++ map snd list]
            ClassEntity c -> make2 True (case fromMaybe
                (error "expected equiv--, disjoint--, sub-- class") mr of
                    SubClass -> subClassOfK
                    EDRelation Equivalent -> equivalentClassesK
                    EDRelation Disjoint -> disjointClassesK
                    _ -> error "bad equiv, disjoint, subClass bit")
                xmlClassExpression c list
            ObjectEntity op -> make2 True (case fromMaybe
                (error "expected domain, range") mr of
                    DRRelation ADomain -> objectPropertyDomainK
                    DRRelation ARange -> objectPropertyRangeK
                    _ -> "bad object domain or range bit") xmlObjProp op list
            SimpleEntity (Entity _ ty ent) -> case ty of
                DataProperty -> make1 True dataPropertyDomainK dataPropertyK
                        mwNameIRI ent list
                NamedIndividual -> make2 False classAssertionK
                        xmlIndividual ent list
                _ -> error "bad expression bit"
    ObjectBit al ->
        let list = xmlAL xmlObjProp al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- obj prop") mr of
                    EDRelation Equivalent -> equivalentObjectPropertiesK
                    EDRelation Disjoint -> disjointObjectPropertiesK
                    _ -> error "bad object bit (equiv, disjoint)"
                ) $ xmlAnnotations anno ++ map snd list]
            ObjectEntity o -> make2 True (case fromMaybe
                (error "expected sub, Inverse, equiv, disjoint op") mr of
                    SubPropertyOf -> subObjectPropertyOfK
                    InverseOf -> inverseObjectPropertiesK
                    EDRelation Equivalent -> equivalentObjectPropertiesK
                    EDRelation Disjoint -> disjointObjectPropertiesK
                    _ -> error "bad object bit (subpropertyof, inverseof)"
                ) xmlObjProp o list
            _ -> error "bad object bit"
    DataBit al ->
        let list = xmlAL (mwNameIRI dataPropertyK) al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- data prop") mr of
                    EDRelation Equivalent -> equivalentDataPropertiesK
                    EDRelation Disjoint -> disjointDataPropertiesK
                    _ -> error "bad data bit"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (Entity _ _ ent) -> make1 True (case fromMaybe
                    (error "expected sub, equiv or disjoint data") mr of
                        SubPropertyOf -> subDataPropertyOfK
                        EDRelation Equivalent -> equivalentDataPropertiesK
                        EDRelation Disjoint -> disjointDataPropertiesK
                        _ -> error "bad data bit"
                    ) dataPropertyK mwNameIRI ent list
            _ -> error "bad data bit"
    IndividualSameOrDifferent al ->
        let list = xmlAL xmlIndividual al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    SDRelation Same -> sameIndividualK
                    SDRelation Different -> differentIndividualsK
                    _ -> error "bad individual bit (s or d)"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (Entity _ _ i) -> make2 True (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    SDRelation Same -> sameIndividualK
                    SDRelation Different -> differentIndividualsK
                    _ -> error "bad individual bit (s or d)"
                ) xmlIndividual i list
            _ -> error "bad individual same or different"
    ObjectCharacteristics al ->
        let ObjectEntity op = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, y) -> makeElement (case y of
                Functional -> functionalObjectPropertyK
                InverseFunctional -> inverseFunctionalObjectPropertyK
                Reflexive -> reflexiveObjectPropertyK
                Irreflexive -> irreflexiveObjectPropertyK
                Symmetric -> symmetricObjectPropertyK
                Asymmetric -> asymmetricObjectPropertyK
                Transitive -> transitiveObjectPropertyK
                Antisymmetric -> antisymmetricObjectPropertyK
            ) $ x ++ [xmlObjProp op]) list
    DataPropRange al ->
        let SimpleEntity (Entity _ DataProperty dp) = ext
            list = xmlAL xmlDataRange al
        in make1 True dataPropertyRangeK dataPropertyK mwNameIRI dp list
    IndividualFacts al ->
        let SimpleEntity (Entity _ NamedIndividual i) = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, f) -> case f of
            ObjectPropertyFact pn op ind ->
               makeElement (case pn of
                    Positive -> objectPropertyAssertionK
                    Negative -> negativeObjectPropertyAssertionK
                ) $ x ++ [xmlObjProp op] ++ map xmlIndividual [i, ind]
            DataPropertyFact pn dp lit ->
                makeElement (case pn of
                    Positive -> dataPropertyAssertionK
                    Negative -> negativeDataPropertyAssertionK
                ) $ x ++ [mwNameIRI dataPropertyK dp] ++
                        [xmlIndividual i] ++ [xmlLiteral lit]
            ) list

xmlAssertion :: IRI -> Annotations -> [Element]
xmlAssertion iri = map (\ (Annotation as ap av) ->
    makeElement annotationAssertionK $ xmlAnnotations as
        ++ [mwNameIRI annotationPropertyK ap]
        ++ [xmlSubject iri, case av of
                AnnValue avalue -> xmlSubject avalue
                AnnValLit l -> xmlLiteral l])

xmlAFB :: Extended -> Annotations -> AnnFrameBit -> [Element]
xmlAFB ext anno afb = case afb of
    AnnotationFrameBit ty -> case ext of
        SimpleEntity ent -> case ty of
            Declaration -> [makeElement declarationK
                    $ xmlAnnotations anno ++ [xmlEntity ent]]
            Assertion -> if null anno then [makeElement declarationK
                                                [xmlEntity ent]]
                          else
                           let Entity _ _ iri = ent in xmlAssertion iri anno
            XmlError _ -> error "xmlAFB"
        Misc ans -> let [Annotation _ iri _] = ans in xmlAssertion iri anno
        ClassEntity ent -> case ent of
            Expression c -> [makeElement declarationK
                    $ xmlAnnotations anno ++ [xmlEntity $ mkEntity Class c]]
            _ -> [] -- very rare cases
        ObjectEntity ent -> case ent of
            ObjectProp o -> [makeElement declarationK
                    $ xmlAnnotations anno ++
                    [xmlEntity $ mkEntity ObjectProperty o]]
            _ -> [] -- very rare cases
    DataFunctional ->
        let SimpleEntity (Entity _ _ dp) = ext
        in [makeElement functionalDataPropertyK
            $ xmlAnnotations anno ++ [mwNameIRI dataPropertyK dp]]
    DatatypeBit dr ->
        let SimpleEntity (Entity _ _ dt) = ext
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

xmlImport :: ImportIRI -> Element
xmlImport i = setName importK $ mwText $ showIRI i

setPref :: String -> Element -> Element
setPref s e = e {elAttribs = Attr {attrKey = makeQN "name"
    , attrVal = s} : elAttribs e}

set1Map :: (String, String) -> Element
set1Map (s, iri) = setPref s $ mwIRI $ splitIRI $ mkIRI iri

xmlPrefixes :: PrefixMap -> [Element]
xmlPrefixes pm = let allpm = Map.union pm predefPrefixes in
    map (setName prefixK . set1Map) $ Map.toList allpm

setOntIRI :: OntologyIRI -> Element -> Element
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
