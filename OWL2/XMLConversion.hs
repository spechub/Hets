{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisionalM
Portability :  portable

Conversion from Manchester syntax to XML Syntax
-}

module OWL2.XMLConversion where

import OWL2.AS
import OWL2.MS
import OWL2.XML
import OWL2.ManchesterPrint

import Text.XML.Light
import Data.Maybe
import Common.Id

import qualified Data.Map as Map

nullQN :: Text.XML.Light.QName
nullQN = QName "" Nothing Nothing

makeQN :: String -> Text.XML.Light.QName
makeQN s = nullQN {qName = s}

setQNPrefix :: String -> Text.XML.Light.QName -> Text.XML.Light.QName
setQNPrefix s qn = qn {qPrefix = Just s}

nullElem :: Element
nullElem = Element nullQN [] [] Nothing

setIRI :: IRI -> Element -> Element
setIRI iri e =
    let ty = if isFullIri iri || null (namePrefix iri) then "IRI"
          else "abbreviatedIRI"
    in e {elAttribs = [Attr {attrKey = makeQN ty, attrVal = showQU iri}]}

setName :: String -> Element -> Element
setName s e = e {elName = nullQN {qName = s,
    qURI = Just "http://www.w3.org/2002/07/owl#"} }

setContent :: [Element] -> Element -> Element
setContent cl e = e {elContent = map Elem cl}

setText :: String -> Element -> Element
setText s e = e {elContent = [Text CData {cdVerbatim = CDataText,
    cdData = s, cdLine = Just 1}]}

setInt :: Int -> Element -> Element
setInt i e = e {elAttribs = [Attr {attrKey = makeQN "cardinality",
    attrVal = show i}]}

setDt :: Bool -> IRI -> Element -> Element
setDt b dt e = e {elAttribs = elAttribs e ++ [Attr {attrKey
    = makeQN (if b then "datatypeIRI" else "facet"), attrVal = showQU dt}]}

setLangTag :: Maybe LanguageTag -> Element -> Element
setLangTag ml e = case ml of
    Nothing -> e
    Just lt -> e {elAttribs = elAttribs e ++ [Attr {attrKey
        = setQNPrefix "xml" (makeQN "lang"), attrVal = lt}]}

mwString :: String -> Element
mwString s = setName s nullElem

mwIRI :: IRI -> Element
mwIRI iri = setIRI iri nullElem

mwNameIRI :: String -> IRI -> Element
mwNameIRI s iri = setName s $ mwIRI iri

mwText :: String -> Element
mwText s = setText s nullElem

mwSimpleIRI :: IRI -> Element
mwSimpleIRI s = setName "IRI" $ mwText $ showQU s

makeElement :: String -> [Element] -> Element
makeElement s el = setContent el $ mwString s

xmlEntity :: Entity -> Element
xmlEntity (Entity ty ent) = mwNameIRI (case ty of
    Class -> "Class"
    Datatype -> "Datatype"
    ObjectProperty -> "ObjectProperty"
    DataProperty -> "DataProperty"
    AnnotationProperty -> "AnnotationProperty"
    NamedIndividual -> "NamedIndividual") ent

xmlLiteral :: Literal -> Element
xmlLiteral (Literal lf tu) =
    let part = setName "Literal" $ mwText lf
    in case tu of
        Typed dt -> setDt True dt part
        Untyped lang -> setLangTag lang $ setDt True (mkQName
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
            part

xmlFVPair :: (ConstrainingFacet, RestrictionValue) -> Element
xmlFVPair (cf, rv) = setDt False cf $ makeElement "FacetRestriction"
    [xmlLiteral rv]

xmlObjProp :: ObjectPropertyExpression -> Element
xmlObjProp ope = case ope of
    ObjectProp op -> mwNameIRI "ObjectProperty" op
    ObjectInverseOf i -> makeElement "ObjectInverseOf" [xmlObjProp i]

xmlDataRange :: DataRange -> Element
xmlDataRange dr = case dr of
    DataType dt cfl ->
        let dtelem = mwNameIRI "Datatype" dt
        in if null cfl then dtelem
            else makeElement "DatatypeRestriction"
            $ dtelem : map xmlFVPair cfl
    DataJunction jt drl -> makeElement (
        case jt of
            IntersectionOf -> "DataIntersectionOf"
            UnionOf -> "DataUnionOf")
        $ map xmlDataRange drl
    DataComplementOf drn -> makeElement "DataComplementOf"
        [xmlDataRange drn]
    DataOneOf ll -> makeElement "DataOneOf"
        $ map xmlLiteral ll

xmlClassExpression :: ClassExpression -> Element
xmlClassExpression ce = case ce of
    Expression c -> mwNameIRI "Class" c
    ObjectJunction jt cel -> makeElement (
        case jt of
            IntersectionOf -> "ObjectIntersectionOf"
            UnionOf -> "ObjectUnionOf")
        $ map xmlClassExpression cel
    ObjectComplementOf cex -> makeElement "ObjectComplementOf"
        [xmlClassExpression cex]
    ObjectOneOf il -> makeElement "ObjectOneOf"
        $ map (mwNameIRI "Individual") il
    ObjectValuesFrom qt ope cex -> makeElement (
        case qt of
            AllValuesFrom -> "ObjectAllValuesFrom"
            SomeValuesFrom -> "ObjectSomeValuesFrom")
        [xmlObjProp ope, xmlClassExpression cex]
    ObjectHasValue ope i -> makeElement "ObjectHasValue"
        [xmlObjProp ope, mwNameIRI "Individual" i]
    ObjectHasSelf ope -> makeElement "ObjectHasSelf" [xmlObjProp ope]
    ObjectCardinality (Cardinality ct i op mce) -> setInt i $ makeElement (
        case ct of
            MinCardinality -> "ObjectMinCardinality"
            MaxCardinality -> "ObjectMaxCardinality"
            ExactCardinality -> "ObjectExactCardinality")
        $ xmlObjProp op :
        case mce of
            Nothing -> []
            Just cexp -> [xmlClassExpression cexp]
    DataValuesFrom qt dp dr -> makeElement (
        case qt of
            AllValuesFrom -> "DataAllValuesFrom"
            SomeValuesFrom -> "DataSomeValuesFrom")
        [mwNameIRI "DataProperty" dp, xmlDataRange dr]
    DataHasValue dp l -> makeElement "DataHasValue"
        [mwNameIRI "DataProperty" dp, xmlLiteral l]
    DataCardinality (Cardinality ct i dp mdr) -> setInt i $ makeElement (
        case ct of
            MinCardinality -> "DataMinCardinality"
            MaxCardinality -> "DataMaxCardinality"
            ExactCardinality -> "DataExactCardinality")
        $ mwNameIRI "DataProperty" dp :
            case mdr of
                Nothing -> []
                Just dr -> [xmlDataRange dr]

xmlAnnotation :: Annotation -> Element
xmlAnnotation (Annotation al ap av) = makeElement "Annotation"
    $ map xmlAnnotation al ++ [mwNameIRI "AnnotationProperty" ap,
    case av of
        AnnValue iri -> mwSimpleIRI iri
        AnnValLit l -> xmlLiteral l]

xmlAnnotations :: Annotations -> [Element]
xmlAnnotations = map xmlAnnotation

xmlAL :: (a -> Element) -> AnnotatedList a -> [([Element], Element)]
xmlAL f al = let annos = map (xmlAnnotations . fst) al 
                 other = map (\ (_, b) -> f b) al
             in zip annos other

make1 :: Bool -> String ->  String -> (String -> IRI -> Element) -> IRI ->
            [([Element], Element)] -> [Element]
make1 rl hdr shdr f iri list = map (\ (a, b) -> makeElement hdr
        $ a ++ (if rl then [f shdr iri, b] else [b, f shdr iri])) list 

make2 :: Bool -> String -> (a -> Element) -> a ->
            [([Element], Element)] -> [Element]
make2 rl hdr f expr list = map (\ (x, y) -> makeElement hdr
        $ x ++ (if rl then [f expr, y] else [y, f expr])) list

xmlLFB :: Extended -> Maybe Relation -> ListFrameBit -> [Element]
xmlLFB ext mr lfb = case lfb of
    AnnotationBit al ->
        let list = xmlAL mwSimpleIRI al
            SimpleEntity (Entity _ ap) = ext
        in case fromMaybe (error "expected domain, range, subproperty") mr of
            SubPropertyOf ->
                let list2 = xmlAL (mwNameIRI "AnnotationProperty") al
                in make1 True "SubAnnotationPropertyOf" "AnnotationProperty"
                         mwNameIRI ap list2
            DRRelation ADomain -> make1 True "SubAnnotationPropertyOf"
                        "AnnotationProperty" mwNameIRI ap list
            DRRelation ARange -> make1 True "SubAnnotationPropertyOf"
                        "AnnotationProperty" mwNameIRI ap list
            _ -> error "bad annotation bit"
    ExpressionBit al ->
        let list = xmlAL xmlClassExpression al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint--, class") mr of
                    EDRelation Equivalent -> "EquivalentClasses"
                    EDRelation Disjoint -> "DisjointClasses"
                    _ -> error "bad equiv or disjoint classes bit"
                ) $ xmlAnnotations anno ++ (map snd list)]
            ClassEntity c -> make2 True (case fromMaybe
                (error "expected equiv--, disjoint--, sub-- class") mr of
                    SubClass -> "SubClassOf"
                    EDRelation Equivalent -> "EquivalentClasses"
                    EDRelation Disjoint -> "DisjointClasses"
                    _ -> error "bad equiv, disjoint, subClass bit")
                xmlClassExpression c list
            ObjectEntity op -> make2 True (case fromMaybe
                (error "expected domain, range") mr of
                    DRRelation ADomain -> "ObjectPropertyDomain"
                    DRRelation ARange -> "ObjectPropertyRange"
                    _ -> "bad object domain or range bit") xmlObjProp op list
            SimpleEntity (Entity ty ent) -> case ty of
                DataProperty -> make1 True "DataPropertyDomain" "DataProperty"
                        mwNameIRI ent list
                NamedIndividual -> make1 False "ClassAssertion"
                        "NamedIndividual" mwNameIRI ent list
                _ -> error "bad expression bit"
    ObjectBit al ->
        let list = xmlAL xmlObjProp al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- obj prop") mr of
                    EDRelation Equivalent -> "EquivalentObjectProperties"
                    EDRelation Disjoint -> "DisjointObjectProperties"
                    _ -> error "bad object bit (equiv, disjoint)"
                ) $ xmlAnnotations anno ++ map snd list]
            ObjectEntity o -> make2 True (case fromMaybe
                (error "expected sub, Inverse, equiv, disjoint op") mr of
                    SubPropertyOf -> "SubObjectPropertyOf"
                    InverseOf -> "InverseObjectProperties"
                    EDRelation Equivalent -> "EquivalentObjectProperties"
                    EDRelation Disjoint -> "DisjointObjectProperties"
                    _ -> error "bad object bit (subpropertyof, inverseof)"
                ) xmlObjProp o list
            _ -> error "bad object bit"
    DataBit al ->
        let list = xmlAL (mwNameIRI "DataProperty") al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected equiv--, disjoint-- data prop") mr of
                    EDRelation Equivalent -> "EquivalentDataProperties"
                    EDRelation Disjoint -> "DisjointDataProperties"
                    _ -> error "bad data bit"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (Entity _ ent) -> make1 True (case fromMaybe
                    (error "expected sub, equiv or disjoint data") mr of
                        SubPropertyOf -> "SubDataPropertyOf"
                        EDRelation Equivalent -> "EquivalentDataProperties"
                        EDRelation Disjoint -> "DisjointDataProperties"
                        _ -> error "bad data bit"
                    ) "DataProperty" mwNameIRI ent list
            _ -> error "bad data bit"
    IndividualSameOrDifferent al ->
        let list = xmlAL (mwNameIRI "NamedIndividual") al in case ext of
            Misc anno -> [makeElement (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    SDRelation Same -> "SameIndividual"
                    SDRelation Different -> "DifferentIndividuals"
                    _ -> error "bad individual bit (s or d)"
                ) $ xmlAnnotations anno ++ map snd list]
            SimpleEntity (Entity _ i) -> make1 True (case fromMaybe
                (error "expected same--, different-- individuals") mr of
                    SDRelation Same -> "SameIndividual"
                    SDRelation Different -> "DifferentIndividuals"
                    _ -> error "bad individual bit (s or d)"
                ) "NamedIndividual" mwNameIRI i list
    ObjectCharacteristics al ->
        let ObjectEntity op = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, y) -> makeElement (case y of
                Functional -> "FunctionalObjectProperty"
                InverseFunctional -> "InverseFunctionalObjectProperty" 
                Reflexive -> "ReflexiveObjectProperty"
                Irreflexive -> "IrreflexiveObjectProperty"
                Symmetric -> "SymmetricObjectProperty"
                Asymmetric -> "AsymmetricObjectProperty"
                Transitive -> "TransitiveObjectProperty"
                Antisymmetric -> "AntisymmetricObjectProperty"
            ) $ x ++ [xmlObjProp op]) list
    DataPropRange al ->
        let SimpleEntity (Entity DataProperty dp) = ext
            list = xmlAL xmlDataRange al
        in make1 True "DataPropertyRange" "DataProperty" mwNameIRI dp list
    IndividualFacts al ->
        let SimpleEntity (Entity NamedIndividual i) = ext
            annos = map (xmlAnnotations . fst) al
            list = zip annos (map snd al)
        in map (\ (x, f) -> case f of
            ObjectPropertyFact pn op ind ->
               makeElement (case pn of
                    Positive -> "ObjectPropertyAssertion"
                    Negative -> "NegativeObjectPropertyAssertion"
                ) $ x ++ [xmlObjProp op]
                        ++ map (mwNameIRI "NamedIndividual") [i, ind]
            DataPropertyFact pn dp lit ->
                makeElement (case pn of
                    Positive -> "DataPropertyAssertion"
                    Negative -> "NegativeDataPropertyAssertion"
                ) $ x ++ [mwNameIRI "DataProperty" dp] ++
                        [mwNameIRI "NamedIndividual" i] ++ [xmlLiteral lit]
            ) list

xmlAFB :: Extended -> Annotations -> AnnFrameBit -> [Element]
xmlAFB ext anno afb = case afb of
    AnnotationFrameBit -> case ext of
        SimpleEntity ent ->
            let Entity ty iri = ent in case ty of
                AnnotationProperty -> map (\ (Annotation as s v) ->
                    makeElement "AnnotationAssertion" $
                        xmlAnnotations as ++ [mwNameIRI "AnnotationProperty" iri]
                            ++ [mwSimpleIRI s, case v of
                                AnnValue avalue -> mwSimpleIRI avalue
                                AnnValLit l -> xmlLiteral l]) anno
                _ -> [makeElement "Declaration"
                    $ xmlAnnotations anno ++ [xmlEntity ent]]
        Misc as ->
            let [Annotation _ ap _] = anno
            in [makeElement "Declaration"
                $ xmlAnnotations as ++ [mwNameIRI "AnnotationProperty" ap]]
        _ -> error "bad ann frane bit"
    DataFunctional ->
        let SimpleEntity (Entity _ dp) = ext
        in [makeElement "FunctionalDataProperty"
            $ xmlAnnotations anno ++ [mwNameIRI "DataProperty" dp]]
    DatatypeBit dr ->
        let SimpleEntity (Entity _ dt) = ext
        in [makeElement "DatatypeDefinition"
                $ xmlAnnotations anno ++ [mwNameIRI "Datatype" dt,
                    xmlDataRange dr]]
    ClassDisjointUnion cel ->
        let ClassEntity c = ext
        in [makeElement "DisjointUnion"
                $ xmlAnnotations anno ++ map xmlClassExpression (c : cel)]
    ClassHasKey op dp ->
        let ClassEntity c = ext
        in [makeElement "HasKey"
                $ xmlAnnotations anno ++ [xmlClassExpression c]
                    ++ map xmlObjProp op ++ map (mwNameIRI "Datatype") dp]
    ObjectSubPropertyChain opl ->
        let ObjectEntity op = ext
            xmlop = map xmlObjProp opl
        in [makeElement "SubObjectPropertyOf"
                $ xmlAnnotations anno ++ [xmlObjProp op,
                    makeElement "ObjectPropertyChain" xmlop]]

xmlFrameBit :: Extended -> FrameBit -> [Element]
xmlFrameBit ext fb = case fb of
    ListFrameBit mr lfb -> xmlLFB ext mr lfb
    AnnFrameBit anno afb -> xmlAFB ext anno afb

xmlAxioms :: Axiom -> [Element]
xmlAxioms (PlainAxiom ext fb) = xmlFrameBit ext fb

xmlFrames :: Frame -> [Element]
xmlFrames (Frame ext fbl) = concatMap (xmlFrameBit ext) fbl

xmlImport :: ImportIRI -> Element
xmlImport i = setName "Import" $ mwText $ showQU i

setPref :: String -> Element -> Element
setPref s e = e {elAttribs = Attr {attrKey = makeQN "name",attrVal = s} : elAttribs e}

set1Map :: (String, String) -> Element
set1Map (s, iri) = setPref s $ mwIRI $ mkQName iri

xmlPrefixes :: PrefixMap -> [Element]
xmlPrefixes pm = map (setName "Prefix" . set1Map) $ Map.toList pm

setXMLNS :: Element -> Element
setXMLNS e = e {elAttribs = Attr {attrKey = makeQN "xmlns", attrVal =
        "http://www.w3.org/2002/07/owl#"} : elAttribs e}

setOntIRI :: OntologyIRI -> Element -> Element
setOntIRI iri e = e {elAttribs = Attr {attrKey = makeQN "ontologyIRI", attrVal =
        showQU iri} : elAttribs e}

xmlOntologyDoc :: OntologyDocument -> Element
xmlOntologyDoc od =
    let ont = ontology od
    in setXMLNS $ setOntIRI (name ont) $ makeElement "Ontology" $
        xmlPrefixes (prefixDeclaration od)
        ++ map xmlImport (imports ont)
        ++ concatMap xmlFrames (ontFrames ont)
        ++ concatMap xmlAnnotations (ann ont) 
