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

import qualified OWL2.AS as AS
import OWL2.MS
import OWL2.Sign
import OWL2.XML
import OWL2.XMLKeywords
import OWL2.Keywords (DatatypeFacet(..))

import Text.XML.Light

import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- | prints the IRI
showIRI :: IRI -> String
showIRI iri = showIRIFull iri {hasAngles = False}

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
                             attrVal = fn $ AS.setReservedPrefix iri}]}

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
correctFacet c = case AS.getPredefName c of
    ">" -> AS.facetToIRINoSign MAXEXCLUSIVE
    "<" -> AS.facetToIRINoSign MINEXCLUSIVE
    ">=" -> AS.facetToIRINoSign MAXINCLUSIVE
    "<=" -> AS.facetToIRINoSign MININCLUSIVE
    _ -> c

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
        AS.Untyped lang -> setLangTag lang $ setDt True AS.plainDatatypeIRI part
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

xmlAnnotations :: [AS.Annotation] -> [Element]
xmlAnnotations = map xmlAnnotation

xmlAssertion :: IRI -> [AS.Annotation] -> [Element]
xmlAssertion iri = map (\ (AS.Annotation as ap av) ->
    makeElement annotationAssertionK $ xmlAnnotations as
        ++ [mwNameIRI annotationPropertyK ap]
        ++ [xmlSubject iri, case av of
                AS.AnnValue avalue -> xmlSubject avalue
                AS.AnnValLit l -> xmlLiteral l])

xmlAxioms :: AS.Axiom -> [Element]
xmlAxioms axiom = case axiom of
    AS.Declaration anns entity -> 
        [makeElement declarationK $ xmlAnnotations anns ++ [xmlEntity entity]]

    AS.ClassAxiom clAxiom -> case clAxiom of
        AS.SubClassOf anns sub sup -> make2 True subClassOfK xmlClassExpression
            sub [(xmlAnnotations anns, xmlClassExpression sup)]
        AS.EquivalentClasses anns ces ->
            [makeElement equivalentClassesK
                $ xmlAnnotations anns ++ map xmlClassExpression ces]
        AS.DisjointClasses anns ces ->
            [makeElement disjointClassesK
                $ xmlAnnotations anns ++ map xmlClassExpression ces]
        AS.DisjointUnion anns clIri ces ->
            [makeElement disjointUnionK $ xmlAnnotations anns
                ++ map xmlClassExpression ((AS.Expression clIri) : ces)]

    AS.ObjectPropertyAxiom opAxiom -> case opAxiom of
        AS.SubObjectPropertyOf anns sub sup -> case sub of
            AS.SubObjPropExpr_obj op ->
                make2 True subObjectPropertyOfK xmlObjProp op
                    [(xmlAnnotations anns, xmlObjProp sup)]
            AS.SubObjPropExpr_exprchain ops ->
                let xmlop = map xmlObjProp ops
                in [makeElement subObjectPropertyOfK
                        $ xmlAnnotations anns
                        ++ [makeElement objectPropertyChainK xmlop
                            , xmlObjProp sup]]

        AS.EquivalentObjectProperties anns ops ->
            [makeElement equivalentObjectPropertiesK
                $ xmlAnnotations anns ++ map xmlObjProp ops]
            
        AS.DisjointObjectProperties anns ops ->
            [makeElement disjointObjectPropertiesK
                $ xmlAnnotations anns ++ map xmlObjProp ops]

        AS.InverseObjectProperties anns op1 op2 ->
            make2 True inverseObjectPropertiesK xmlObjProp op1
                [(xmlAnnotations anns, xmlObjProp op2)]

        AS.ObjectPropertyDomain anns op ce ->
            make2 True objectPropertyDomainK xmlObjProp op
                [(xmlAnnotations anns, xmlClassExpression ce)]

        AS.ObjectPropertyRange anns op ce ->
            make2 True objectPropertyRangeK xmlObjProp op
                [(xmlAnnotations anns, xmlClassExpression ce)]

        AS.FunctionalObjectProperty anns op -> 
            [makeElement functionalObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.InverseFunctionalObjectProperty anns op ->
            [makeElement inverseFunctionalObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.ReflexiveObjectProperty anns op ->
            [makeElement reflexiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.IrreflexiveObjectProperty anns op ->
            [makeElement irreflexiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.SymmetricObjectProperty anns op ->
            [makeElement symmetricObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.AsymmetricObjectProperty anns op ->
            [makeElement asymmetricObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

        AS.TransitiveObjectProperty anns op ->
            [makeElement transitiveObjectPropertyK
                $ xmlAnnotations anns ++ [xmlObjProp op]]

    AS.DataPropertyAxiom dpAxiom -> case dpAxiom of
        AS.SubDataPropertyOf anns sub sup -> 
            make1 True subDataPropertyOfK dataPropertyK
                mwNameIRI sub [(xmlAnnotations anns, mwNameIRI dataPropertyK sup)]

        AS.EquivalentDataProperties anns dps ->
            [makeElement equivalentDataPropertiesK
                $ xmlAnnotations anns ++ map (mwNameIRI dataPropertyK) dps]

        AS.DisjointDataProperties anns dps ->
            [makeElement disjointDataPropertiesK
                $ xmlAnnotations anns ++ map (mwNameIRI dataPropertyK) dps]

        AS.DataPropertyDomain anns dpe ce ->
            make1 True dataPropertyDomainK dataPropertyK mwNameIRI dpe
                [(xmlAnnotations anns, xmlClassExpression ce)]

        AS.DataPropertyRange anns dpe dr -> 
            make1 True dataPropertyRangeK dataPropertyK mwNameIRI dpe
                [(xmlAnnotations anns, xmlDataRange dr)]

        AS.FunctionalDataProperty anns dpe ->
            [makeElement functionalDataPropertyK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dpe]]

    AS.DatatypeDefinition anns dt dr ->
        [makeElement datatypeDefinitionK $ xmlAnnotations anns
            ++ [mwNameIRI datatypeK dt, xmlDataRange dr]]

    AS.HasKey anns ce ops dps -> 
        [makeElement hasKeyK $ xmlAnnotations anns ++ [xmlClassExpression ce]
            ++ map xmlObjProp ops ++ map (mwNameIRI dataPropertyK) dps]

    AS.Assertion aAxiom -> case aAxiom of
        AS.SameIndividual anns inds ->
            [makeElement sameIndividualK
                $ xmlAnnotations anns ++ map xmlIndividual inds]

        AS.DifferentIndividuals anns inds ->
            [makeElement differentIndividualsK
                $ xmlAnnotations anns ++ map xmlIndividual inds]

        AS.ClassAssertion anns ce ind ->
            make2 False classAssertionK xmlIndividual ind
                [(xmlAnnotations anns, xmlClassExpression ce)]

        AS.ObjectPropertyAssertion anns op sInd tInd ->
            [makeElement objectPropertyAssertionK
                $ xmlAnnotations anns ++ [xmlObjProp op]
                ++ map xmlIndividual [sInd, tInd]]

        AS.NegativeObjectPropertyAssertion anns op sInd tInd ->
            [makeElement negativeObjectPropertyAssertionK
                $ xmlAnnotations anns ++ [xmlObjProp op]
                ++ map xmlIndividual [sInd, tInd]]

        AS.DataPropertyAssertion anns dp sInd tVal ->
            [makeElement dataPropertyAssertionK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dp]
                ++ [xmlIndividual sInd] ++ [xmlLiteral tVal]]

        AS.NegativeDataPropertyAssertion anns dp sInd tVal ->
            [makeElement negativeDataPropertyAssertionK
                $ xmlAnnotations anns ++ [mwNameIRI dataPropertyK dp]
                ++ [xmlIndividual sInd] ++ [xmlLiteral tVal]]

    AS.AnnotationAxiom annAxiom -> case annAxiom of
        AS.AnnotationAssertion anns prop subj value -> 
            let iri = case subj of
                    AS.AnnSubIri i -> i
                    AS.AnnSubAnInd i -> i
            in xmlAssertion iri [AS.Annotation anns prop value]

        AS.SubAnnotationPropertyOf anns sub sup ->
            make1 True subAnnotationPropertyOfK annotationPropertyK
                mwNameIRI sub
                [(xmlAnnotations anns, mwNameIRI annotationPropertyK sup)]

        AS.AnnotationPropertyDomain anns prop iri ->
            make1 True annotationPropertyDomainK
                annotationPropertyK mwNameIRI prop
                [(xmlAnnotations anns, mwSimpleIRI iri)]

        AS.AnnotationPropertyRange anns prop iri ->
            make1 True annotationPropertyRangeK
                annotationPropertyK mwNameIRI prop
                [(xmlAnnotations anns, mwSimpleIRI iri)]


    AS.Rule rule -> case rule of
        AS.DLSafeRule anns body head -> 
            [makeElement dlSafeRuleK $ xmlAnnotations anns
                ++ [makeElement "Body" $ map xmlAtom body
                    , makeElement "Head" $ map xmlAtom head]] 
        AS.DGRule _ _ _ -> error "DG Rules are not supported in XML yet"
    AS.DGAxiom _ _ _ _ _ -> error "DG Axioms are not supported in XML yet"

xmlAtom :: AS.Atom -> Element
xmlAtom atom = case atom of
    AS.ClassAtom ce ia -> makeElement classAtomK
        [xmlClassExpression ce, xmlIndividualArg ia]

    AS.DataRangeAtom dr da -> makeElement dataRangeAtomK
        [xmlDataRange dr, xmlDataArg da]

    AS.ObjectPropertyAtom oe ia1 ia2 -> makeElement objectPropertyAtomK
        [xmlObjProp oe, xmlIndividualArg ia1, xmlIndividualArg ia2]

    AS.DataPropertyAtom dp ia da -> makeElement dataPropertyAtomK
        [mwNameIRI dataPropertyK dp, xmlIndividualArg ia, xmlDataArg da]

    AS.BuiltInAtom iri das -> makeElement builtInAtomK 
        $ (mwNameIRI "IRI" iri) : map xmlDataArg das
    -- prefered way - iri is an child element
    -- <builtInAtomK>
    --     <IRI iri="iri">
    --     <DataArg>
    --     <DataArg>

    AS.SameIndividualAtom ia1 ia2 -> makeElement sameIndividualAtomK
        . map xmlIndividualArg $ [ia1, ia2]

    AS.DifferentIndividualsAtom ia1 ia2 -> makeElement differentIndividualsAtomK
        . map xmlIndividualArg $ [ia1, ia2]

    _ -> error "XML Converter: Uknown atom"


xmlIndividualArg :: AS.IndividualArg -> Element
xmlIndividualArg ia = case ia of
    AS.IArg i -> mwNameIRI individualArgumentK i
    AS.IVar i -> mwNameIRI individualVariableK i

xmlDataArg :: AS.DataArg -> Element
xmlDataArg da = case da of
    AS.DArg lit -> xmlLiteral lit
    AS.DVar iri -> mwNameIRI dataVariableK iri

xmlUnknownArg :: AS.UnkownArg -> Element
xmlUnknownArg ua = case ua of
    AS.IndividualArg ia -> xmlIndividualArg ia
    AS.DataArg da -> xmlDataArg da
    AS.Variable v -> mwNameIRI variableK v

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

set1Map :: (String, IRI) -> Element
set1Map (s, iri) = setPref s $ mwIRI iri

xmlPrefixes :: GA.PrefixMap -> [Element]
xmlPrefixes pm = let allpm = Map.union pm $ AS.predefPrefixesGA in
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

xmlOntologyDoc :: Sign -> AS.OntologyDocument -> Element
xmlOntologyDoc s od =
    let ont = AS.ontology od
        pd = AS.prefixDeclaration od
        emptyPref = showIRI $ fromMaybe dummyIRI $ Map.lookup "" pd
    in setBase emptyPref $ setXMLNS
        $ setOntIRI (fromMaybe dummyIRI $ AS.mOntologyIRI ont)
        $ makeElement "Ontology" $ xmlPrefixes pd
            ++ map xmlImport (AS.importsDocuments ont)
            ++ concatMap xmlAxioms (AS.axioms ont) -- change xmlFrames 
            ++ concatMap xmlAnnotations [(AS.ontologyAnnotation ont)]
            ++ signToDec s

-- TODO: commented out in 1993
mkODoc :: Sign -> [Named AS.Axiom] -> String
mkODoc s = ppTopElement . xmlOntologyDoc s
    . AS.OntologyDocument (AS.OntologyMetadata AS.AS) (AS.changePrefixMapTypeToGA $ prefixMap s)
    . AS.Ontology Nothing Nothing [] [] . map sentence
