module OWL2.XMLConversion where

import OWL2.AS
import OWL2.MS
import OWL2.XML
import OWL2.ManchesterPrint
import Text.XML.Light
import Data.Maybe

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

xmlLiteral :: Literal -> Element
xmlLiteral (Literal lf tu) =
  let part = setName "Literal" $ mwText lf
  in case tu of
    Typed dt -> setDt True dt part
    Untyped lang -> setLangTag lang $ setDt True
      (mkQName "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
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
      UnionOf -> "DataUnionOf" )
    $ map xmlDataRange drl
  DataComplementOf dr -> makeElement "DataComplementOf"
       [xmlDataRange dr]
  DataOneOf ll -> makeElement "DataOneOf"
    $ map xmlLiteral ll

xmlClassExpression :: ClassExpression -> Element
xmlClassExpression ce = case ce of
  Expression c -> mwNameIRI "Class" c
  ObjectJunction jt cel -> makeElement (
    case jt of
      IntersectionOf -> "ObjectIntersectionOf"
      UnionOf -> "ObjectUnionOf" )
    $ map xmlClassExpression cel
  ObjectComplementOf ce -> makeElement "ObjectComplementOf"
        [xmlClassExpression ce]
  ObjectOneOf il -> makeElement "ObjectOneOf"
    $ map (mwNameIRI "Individual") il
  ObjectValuesFrom qt ope ce -> makeElement (
    case qt of
       AllValuesFrom -> "ObjectAllValuesFrom"
       SomeValuesFrom -> "ObjectSomeValuesFrom" )
        [xmlObjProp ope, xmlClassExpression ce]
  ObjectHasValue ope i -> makeElement "ObjectHasValue"
        [xmlObjProp ope, mwNameIRI "Individual" i]
  ObjectHasSelf ope -> makeElement "ObjectHasSelf" [xmlObjProp ope]
  ObjectCardinality (Cardinality ct i op mce) -> setInt i $ makeElement (
    case ct of
        MinCardinality -> "ObjectMinCardinality"
        MaxCardinality -> "ObjectMaxCardinality"
        ExactCardinality -> "ObjectExactCardinality" )
    $ xmlObjProp op :
      case mce of
          Nothing -> []
          Just ce -> [xmlClassExpression ce]
  DataValuesFrom qt dp dr -> makeElement (
    case qt of
       AllValuesFrom -> "DataAllValuesFrom"
       SomeValuesFrom -> "DataSomeValuesFrom" )
        [mwNameIRI "DataProperty" dp, xmlDataRange dr]
  DataHasValue dp l -> makeElement "DataHasValue"
        [mwNameIRI "DataProperty" dp, xmlLiteral l]
  DataCardinality (Cardinality ct i dp mdr) -> setInt i $ makeElement (
    case ct of
        MinCardinality -> "DataMinCardinality"
        MaxCardinality -> "DataMaxCardinality"
        ExactCardinality -> "DataExactCardinality" )
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

xmlAL :: (a -> Element) -> AnnotatedList a -> ([Element], [Element])
xmlAL f al = (concatMap (xmlAnnotations . fst) al , map (\ (_, b) -> f b) al)

xmlLFB :: Extended -> Maybe Relation -> ListFrameBit -> Element
xmlLFB ext mr lfb = case lfb of
  AnnotationBit al ->
    let (as, apelem) = xmlAL (mwNameIRI "AnnotationProperty") al
        (as2, apelem2) = xmlAL mwSimpleIRI al
        SimpleEntity (Entity _ ap) = ext
    in case fromMaybe (error "expected domain, range, subproperty of") mr of
      SubPropertyOf -> makeElement "SubAnnotationPropertyOf" $
        as ++ [mwNameIRI "AnnotationProperty" ap] ++ apelem
      DRRelation ADomain -> makeElement "AnnotationPropertyDomain" $
        as2 ++ [mwNameIRI "AnnotationProperty" ap] ++ apelem2
      DRRelation ARange -> makeElement "AnnotationPropertyRange" $
        as2 ++ [mwNameIRI "AnnotationProperty" ap] ++ apelem2
  ExpressionBit al -> 
    let (as, cel) = xmlAL xmlClassExpression al in case ext of
      Misc anno -> makeElement (case fromMaybe 
          (error "expected equiv--, disjoint--, sub-- class") mr of
            EDRelation Equivalent -> "EquivalentClasses"
            EDRelation Disjoint -> "DisjointClasses"
        ) $ xmlAnnotations anno ++ cel
      ClassEntity c -> makeElement "SubClassOf"
          $ as ++ [xmlClassExpression c] ++ cel
      ObjectEntity op -> makeElement (case fromMaybe 
          (error "expected domain, range") mr of
            DRRelation ADomain -> "ObjectPropertyDomain"
            DRRelation ARange -> "ObjectPropertyRange"
        ) $ as ++ [xmlObjProp op] ++ cel
      SimpleEntity (Entity ty ent) -> case ty of
        DataProperty -> makeElement "DataPropertyDomain"
          $ as ++ [mwNameIRI "DataProperty" ent] ++ cel
        NamedIndividual -> makeElement "ClassAssertion"
          $ as ++ cel ++ [mwNameIRI "NamedIndividual" ent]












