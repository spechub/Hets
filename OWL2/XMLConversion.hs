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
import Common.GlobalAnnotations as GA (PrefixMap)
import Common.IRI hiding (showIRI)
import Common.Id

import OWL2.AS
import OWL2.Sign
import OWL2.XMLKeywords
import OWL2.Keywords (DatatypeFacet(..))

import Text.XML.Light

import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- | prints the IRI
showIRI :: IRI -> String
showIRI iri = (if isURN iri then showURN else showIRIFull) iri {hasAngles = False}

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
    let (ty, fn)
            | isAbbrev iri = ("abbreviatedIRI", showIRICompact)
            | isBlankNode iri = (nodeID, showIRI)
            | otherwise = (iriK, showIRI)
    in e {elAttribs = [Attr {attrKey = makeQN ty,
                             attrVal = fn $ setReservedPrefix iri}]}

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
correctFacet c = case getPredefName c of
    ">" -> facetToIRINoSign MAXEXCLUSIVE
    "<" -> facetToIRINoSign MINEXCLUSIVE
    ">=" -> facetToIRINoSign MAXINCLUSIVE
    "<=" -> facetToIRINoSign MININCLUSIVE
    _ -> c

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
        Untyped lang -> setLangTag lang $ setDt True plainDatatypeIRI part
  NumberLit f -> setDt True (nullIRI {iriScheme = "http:",
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
        [mwNameIRI dataPropertyK (head dp), xmlDataRange dr]
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
        AnnValLit l -> xmlLiteral l
        AnnAnInd iri -> xmlSubject iri]

xmlSubject :: IRI -> Element
xmlSubject iri = if isAnonymous iri then xmlIndividual iri
                  else mwSimpleIRI iri

xmlAnnotations :: [Annotation] -> [Element]
xmlAnnotations = map xmlAnnotation

xmlAssertion :: IRI -> [Annotation] -> [Element]
xmlAssertion iri = map (\ (Annotation as ap av) ->
    makeElement annotationAssertionK $ xmlAnnotations as
        ++ [mwNameIRI annotationPropertyK ap]
        ++ [xmlSubject iri, case av of
                AnnValue avalue -> xmlSubject avalue
                AnnAnInd ind -> xmlSubject ind
                AnnValLit l -> xmlLiteral l])

xmlAxioms :: Axiom -> [Element]
xmlAxioms axiom = case axiom of
    Declaration anns entity -> 
        [makeElement declarationK $ xmlAnnotations anns ++ [xmlEntity entity]]

    ClassAxiom clAxiom -> case clAxiom of
        SubClassOf anns sub sup -> make2 True subClassOfK xmlClassExpression
            sub [(xmlAnnotations anns, xmlClassExpression sup)]
        EquivalentClasses anns ces ->
            [makeElement equivalentClassesK
                $ xmlAnnotations anns ++ map xmlClassExpression ces]
        DisjointClasses anns ces ->
            [makeElement disjointClassesK
                $ xmlAnnotations anns ++ map xmlClassExpression ces]
        DisjointUnion anns clIri ces ->
            [makeElement disjointUnionK $ xmlAnnotations anns
                ++ map xmlClassExpression ((Expression clIri) : ces)]

    ObjectPropertyAxiom opAxiom -> case opAxiom of
        SubObjectPropertyOf anns sub sup -> case sub of
            SubObjPropExpr_obj op ->
                make2 True subObjectPropertyOfK xmlObjProp op
                    [(xmlAnnotations anns, xmlObjProp sup)]
            SubObjPropExpr_exprchain ops ->
                let xmlop = map xmlObjProp ops
                in [makeElement subObjectPropertyOfK
                        $ xmlAnnotations anns
                        ++ [makeElement objectPropertyChainK xmlop
                            , xmlObjProp sup]]

        EquivalentObjectProperties anns ops ->
            [makeElement equivalentObjectPropertiesK
                $ xmlAnnotations anns ++ map xmlObjProp ops]
            
        DisjointObjectProperties anns ops ->
            [makeElement disjointObjectPropertiesK
                $ xmlAnnotations anns ++ map xmlObjProp ops]

        InverseObjectProperties anns op1 op2 ->
            make2 True inverseObjectPropertiesK xmlObjProp op1
                [(xmlAnnotations anns, xmlObjProp op2)]

        ObjectPropertyDomain anns op ce ->
            make2 True objectPropertyDomainK xmlObjProp op
                [(xmlAnnotations anns, xmlClassExpression ce)]

        ObjectPropertyRange anns op ce ->
            make2 True objectPropertyRangeK xmlObjProp op
                [(xmlAnnotations anns, xmlClassExpression ce)]

        FunctionalObjectProperty anns op -> 
            [makeElement functionalObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        InverseFunctionalObjectProperty anns op ->
            [makeElement inverseFunctionalObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        ReflexiveObjectProperty anns op ->
            [makeElement reflexiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        IrreflexiveObjectProperty anns op ->
            [makeElement irreflexiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        SymmetricObjectProperty anns op ->
            [makeElement symmetricObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AsymmetricObjectProperty anns op ->
            [makeElement asymmetricObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        TransitiveObjectProperty anns op ->
            [makeElement transitiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

    DataPropertyAxiom dpAxiom -> case dpAxiom of
        SubDataPropertyOf anns sub sup -> 
            make1 True subDataPropertyOfK dataPropertyK
                mwNameIRI sub [(xmlAnnotations anns, mwNameIRI dataPropertyK sup)]

        EquivalentDataProperties anns dps ->
            [makeElement equivalentDataPropertiesK
                $ xmlAnnotations anns ++ map (mwNameIRI dataPropertyK) dps]

        DisjointDataProperties anns dps ->
            [makeElement disjointDataPropertiesK
                $ xmlAnnotations anns ++ map (mwNameIRI dataPropertyK) dps]

        DataPropertyDomain anns dpe ce ->
            make1 True dataPropertyDomainK dataPropertyK mwNameIRI dpe
                [(xmlAnnotations anns, xmlClassExpression ce)]

        DataPropertyRange anns dpe dr -> 
            make1 True dataPropertyRangeK dataPropertyK mwNameIRI dpe
                [(xmlAnnotations anns, xmlDataRange dr)]

        FunctionalDataProperty anns dpe ->
            [makeElement functionalDataPropertyK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dpe]]

    DatatypeDefinition anns dt dr ->
        [makeElement datatypeDefinitionK $ xmlAnnotations anns
            ++ [mwNameIRI datatypeK dt, xmlDataRange dr]]

    HasKey anns ce ops dps -> 
        [makeElement hasKeyK $ xmlAnnotations anns ++ [xmlClassExpression ce]
            ++ map xmlObjProp ops ++ map (mwNameIRI dataPropertyK) dps]

    Assertion aAxiom -> case aAxiom of
        SameIndividual anns inds ->
            [makeElement sameIndividualK
                $ xmlAnnotations anns ++ map xmlIndividual inds]

        DifferentIndividuals anns inds ->
            [makeElement differentIndividualsK
                $ xmlAnnotations anns ++ map xmlIndividual inds]

        ClassAssertion anns ce ind ->
            make2 False classAssertionK xmlIndividual ind
                [(xmlAnnotations anns, xmlClassExpression ce)]

        ObjectPropertyAssertion anns op sInd tInd ->
            [makeElement objectPropertyAssertionK
                $ xmlAnnotations anns ++ [xmlObjProp op]
                ++ map xmlIndividual [sInd, tInd]]

        NegativeObjectPropertyAssertion anns op sInd tInd ->
            [makeElement negativeObjectPropertyAssertionK
                $ xmlAnnotations anns ++ [xmlObjProp op]
                ++ map xmlIndividual [sInd, tInd]]

        DataPropertyAssertion anns dp sInd tVal ->
            [makeElement dataPropertyAssertionK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dp]
                ++ [xmlIndividual sInd] ++ [xmlLiteral tVal]]

        NegativeDataPropertyAssertion anns dp sInd tVal ->
            [makeElement negativeDataPropertyAssertionK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dp]
                ++ [xmlIndividual sInd] ++ [xmlLiteral tVal]]

    AnnotationAxiom annAxiom -> case annAxiom of
        AnnotationAssertion anns prop subj value -> 
            let iri = case subj of
                    AnnSubIri i -> i
                    AnnSubAnInd i -> i
            in xmlAssertion iri [Annotation anns prop value]

        SubAnnotationPropertyOf anns sub sup ->
            make1 True subAnnotationPropertyOfK annotationPropertyK
                mwNameIRI sub
                [(xmlAnnotations anns, mwNameIRI annotationPropertyK sup)]

        AnnotationPropertyDomain anns prop iri ->
            make1 True annotationPropertyDomainK
                annotationPropertyK mwNameIRI prop
                [(xmlAnnotations anns, mwSimpleIRI iri)]

        AnnotationPropertyRange anns prop iri ->
            make1 True annotationPropertyRangeK
                annotationPropertyK mwNameIRI prop
                [(xmlAnnotations anns, mwSimpleIRI iri)]


    Rule rule -> case rule of
        DLSafeRule anns bd hd -> 
            [makeElement dlSafeRuleK $ xmlAnnotations anns
                ++ [makeElement "Body" $ map xmlAtom bd
                    , makeElement "Head" $ map xmlAtom hd]] 
        DGRule _ _ _ -> error "DG Rules are not supported in XML yet"
    DGAxiom _ _ _ _ _ -> error "DG Axioms are not supported in XML yet"

xmlAtom :: Atom -> Element
xmlAtom atom = case atom of
    ClassAtom ce ia -> makeElement classAtomK
        [xmlClassExpression ce, xmlIndividualArg ia]

    DataRangeAtom dr da -> makeElement dataRangeAtomK
        [xmlDataRange dr, xmlDataArg da]

    ObjectPropertyAtom oe ia1 ia2 -> makeElement objectPropertyAtomK
        [xmlObjProp oe, xmlIndividualArg ia1, xmlIndividualArg ia2]

    DataPropertyAtom dp ia da -> makeElement dataPropertyAtomK
        [mwNameIRI dataPropertyK dp, xmlIndividualArg ia, xmlDataArg da]

    BuiltInAtom iri das -> setIRI iri $ makeElement builtInAtomK 
        $ map xmlDataArg das

    SameIndividualAtom ia1 ia2 -> makeElement sameIndividualAtomK
        . map xmlIndividualArg $ [ia1, ia2]

    DifferentIndividualsAtom ia1 ia2 -> makeElement differentIndividualsAtomK
        . map xmlIndividualArg $ [ia1, ia2]

    _ -> error "XML Converter: Uknown atom"


xmlIndividualArg :: IndividualArg -> Element
xmlIndividualArg ia = case ia of
    IArg i -> mwNameIRI namedIndividualK i
    IVar i -> mwNameIRI variableK i

xmlDataArg :: DataArg -> Element
xmlDataArg da = case da of
    DArg lit -> xmlLiteral lit
    DVar iri -> mwNameIRI variableK iri

xmlUnknownArg :: UnkownArg -> Element
xmlUnknownArg ua = case ua of
    IndividualArg ia -> xmlIndividualArg ia
    DataArg da -> xmlDataArg da
    Variable v -> mwNameIRI variableK v

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

set1Map :: (String, IRI) -> Element
set1Map (s, iri) = setPref s $ mwIRI iri

xmlPrefixes :: GA.PrefixMap -> [Element]
xmlPrefixes pm = let allpm = Map.union pm $ predefPrefixesGA in
    map (setName prefixK . set1Map) $ Map.toList allpm

setOntIRI :: Maybe OntologyIRI -> Element -> Element
setOntIRI mIri e = case mIri of
    Nothing -> e
    Just iri -> e { elAttribs = Attr {
        attrKey = makeQN "ontologyIRI"
      , attrVal = showIRI iri } : elAttribs e }

setOntVersionIRI :: Maybe OntologyIRI -> Element -> Element
setOntVersionIRI mIri e = case mIri of
    Nothing -> e
    Just iri -> e { elAttribs = Attr {
        attrKey = makeQN "versionIRI"
      , attrVal = showIRI iri } : elAttribs e }

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
        emptyPref = showIRI $ fromMaybe dummyIRI $ Map.lookup "" pd
    in setBase emptyPref $ setXMLNS
        $ setOntIRI (mOntologyIRI ont)
        $ setOntVersionIRI (mOntologyVersion ont)
        $ makeElement "Ontology" $ xmlPrefixes pd
            ++ map xmlImport (importsDocuments ont)
            ++ concatMap xmlAxioms (axioms ont) -- change xmlFrames 
            ++ concatMap xmlAnnotations [(ontologyAnnotation ont)]
            ++ signToDec s

-- TODO: commented out in 1993
mkODoc :: Sign -> [Named Axiom] -> String
mkODoc s = ppTopElement . xmlOntologyDoc s
    . OntologyDocument (OntologyMetadata AS) (changePrefixMapTypeToGA $ prefixMap s)
    . Ontology Nothing Nothing [] [] . map sentence
