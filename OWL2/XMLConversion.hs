module OWL2.XMLConversion where

import OWL2.AS
import OWL2.MS
import OWL2.XML

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

makeNewName :: String -> Element
makeNewName s = setName s nullElem

makeNewIRI :: IRI -> Element
makeNewIRI iri = setIRI iri nullElem

makeIRIWithName :: String -> IRI -> Element
makeIRIWithName s iri = setName s $ makeNewIRI iri

makeElemWithText :: String -> Element
makeElemWithText s = setText s nullElem

makeNewElement :: String -> [Element] -> Element
makeNewElement s el = setContent el $ makeNewName s

xmlLiteral :: Literal -> Element
xmlLiteral (Literal lf tu) =
  let part = setName "Literal" $ makeElemWithText lf
  in case tu of
    Typed dt -> setDt True dt part
    Untyped lang -> setLangTag lang $ setDt True
      (mkQName "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
      part

xmlFVPair :: (ConstrainingFacet, RestrictionValue) -> Element
xmlFVPair (cf, rv) = setDt False cf $ makeNewElement "FacetRestriction"
    [xmlLiteral rv]

xmlObjProp :: ObjectPropertyExpression -> Element
xmlObjProp ope = case ope of
  ObjectProp op -> makeIRIWithName "ObjectProperty" op
  ObjectInverseOf i -> makeNewElement "ObjectInverseOf" [xmlObjProp i]

xmlDataRange :: DataRange -> Element
xmlDataRange dr = case dr of
  DataType dt cfl ->
    let dtelem = makeIRIWithName "Datatype" dt
    in if null cfl then dtelem
        else makeNewElement "DatatypeRestriction"
          $ dtelem : map xmlFVPair cfl
  DataJunction jt drl -> makeNewElement (
    case jt of
      IntersectionOf -> "DataIntersectionOf"
      UnionOf -> "DataUnionOf" )
    $ map xmlDataRange drl
  DataComplementOf dr -> makeNewElement "DataComplementOf"
       [xmlDataRange dr]
  DataOneOf ll -> makeNewElement "DataOneOf"
    $ map xmlLiteral ll

xmlClassExpression :: ClassExpression -> Element
xmlClassExpression ce = case ce of
  Expression c -> makeIRIWithName "Class" c
  ObjectJunction jt cel -> makeNewElement (
    case jt of
      IntersectionOf -> "ObjectIntersectionOf"
      UnionOf -> "ObjectUnionOf" )
    $ map xmlClassExpression cel
  ObjectComplementOf ce -> makeNewElement "ObjectComplementOf"
        [xmlClassExpression ce]
  ObjectOneOf il -> makeNewElement "ObjectOneOf"
    $ map (makeIRIWithName "Individual") il
  ObjectValuesFrom qt ope ce -> makeNewElement (
    case qt of
       AllValuesFrom -> "ObjectAllValuesFrom"
       SomeValuesFrom -> "ObjectSomeValuesFrom" )
        [xmlObjProp ope, xmlClassExpression ce]
  ObjectHasValue ope i -> makeNewElement "ObjectHasValue"
        [xmlObjProp ope, makeIRIWithName "Individual" i]
  ObjectHasSelf ope -> makeNewElement "ObjectHasSelf" [xmlObjProp ope]
  ObjectCardinality (Cardinality ct i op mce) -> setInt i $ makeNewElement (
    case ct of
        MinCardinality -> "ObjectMinCardinality"
        MaxCardinality -> "ObjectMaxCardinality"
        ExactCardinality -> "ObjectExactCardinality" )
    $ xmlObjProp op :
      case mce of
          Nothing -> []
          Just ce -> [xmlClassExpression ce]
  DataValuesFrom qt dp dr -> makeNewElement (
    case qt of
       AllValuesFrom -> "DataAllValuesFrom"
       SomeValuesFrom -> "DataSomeValuesFrom" )
        [makeIRIWithName "DataProperty" dp, xmlDataRange dr]
  DataHasValue dp l -> makeNewElement "DataHasValue"
        [makeIRIWithName "DataProperty" dp, xmlLiteral l]
  DataCardinality (Cardinality ct i dp mdr) -> setInt i $ makeNewElement (
    case ct of
        MinCardinality -> "DataMinCardinality"
        MaxCardinality -> "DataMaxCardinality"
        ExactCardinality -> "DataExactCardinality" )
    $ makeIRIWithName "DataProperty" dp :
      case mdr of
          Nothing -> []
          Just dr -> [xmlDataRange dr]













