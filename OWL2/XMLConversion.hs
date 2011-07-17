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

nullElem :: Element
nullElem = Element nullQN [] [] Nothing

setContent :: [Element] -> Element -> Element
setContent cl e = e {elContent = map Elem cl}

setNewElement :: String -> [Element] -> Element
setNewElement s el = setContent el $ setNew s

setName :: String -> Element -> Element
setName s e = e {elName = nullQN {qName = s,
        qURI = Just "http://www.w3.org/2002/07/owl#"} }

setNew :: String -> Element
setNew s = setName s nullElem

setIRI :: IRI -> Element -> Element
setIRI iri e =
  let f = isFullIri iri
      np = namePrefix iri
      lp = localPart iri
      ty = if f || null np then "IRI"
            else "abbreviatedIRI"
      s = if null np then lp
           else np ++ ":" ++ lp
  in e {elAttribs = [Attr {attrKey = makeQN ty, attrVal = s}]}

setNewIRI :: IRI -> Element
setNewIRI iri = setIRI iri nullElem

setIRIWithName :: String -> IRI -> Element
setIRIWithName s iri = setName s $ setNewIRI iri

setInt :: Int -> Element -> Element
setInt i e = e {elAttribs = [Attr {attrKey = makeQN "cardinality",
  attrVal = show i}]}

toObjProp :: ObjectPropertyExpression -> Element
toObjProp ope = case ope of
  ObjectProp op -> setName "ObjectProperty" $ setIRI op nullElem
  ObjectInverseOf i -> setNewElement "ObjectInverseOf" [toObjProp i]

toDataRange :: DataRange -> Element
toDataRange dr = case dr of
  DataJunction jt drl -> setNewElement (
    case jt of
      IntersectionOf ->  "DataIntersectionOf"
      UnionOf -> "DataUnionOf" )
    $ map toDataRange drl
  DataComplementOf dr -> setNewElement "DataComplementOf"
       [toDataRange dr]

toClassExpression :: ClassExpression -> Element
toClassExpression ce = case ce of
  Expression c -> setIRIWithName "Class" c
  ObjectJunction jt cel -> setNewElement (
    case jt of
      IntersectionOf ->  "ObjectIntersectionOf"
      UnionOf -> "ObjectUnionOf" )
    $ map toClassExpression cel
  ObjectComplementOf ce -> setNewElement "ObjectComplementOf"
        [toClassExpression ce]
  ObjectOneOf il -> setNewElement "ObjectOneOf" $ map (setIRIWithName "Individual") il
  ObjectValuesFrom qt ope ce -> setNewElement (
    case qt of
       AllValuesFrom -> "ObjectAllValuesFrom"
       SomeValuesFrom -> "ObjectSomeValuesFrom" )
        [toObjProp ope, toClassExpression ce]
  ObjectHasValue ope i -> setNewElement "ObjectHasValue"
        [toObjProp ope, setIRIWithName "Individual" i]
  ObjectHasSelf ope -> setNewElement "ObjectHasSelf" [toObjProp ope]
  ObjectCardinality (Cardinality ct i op mce) -> setInt i $ setNewElement ( 
    case ct of 
        MinCardinality -> "ObjectMinCardinality"
        MaxCardinality -> "ObjectMaxCardinality"
        ExactCardinality -> "ObjectExactCardinality" )
    $ toObjProp op :
      case mce of 
          Nothing -> []
          Just ce -> [toClassExpression ce]
  DataValuesFrom qt dp dr -> setNewElement (
    case qt of
       AllValuesFrom -> "DataAllValuesFrom"
       SomeValuesFrom -> "DataSomeValuesFrom" )
        [setIRIWithName "DataProperty" dp, toDataRange dr]
 -- DataHasValue dp l -> setNewElement "DataHasValue"
  --      [setIRIWithName "DataProperty" dp, setLiteral l]
  DataCardinality (Cardinality ct i dp mdr) -> setInt i $ setNewElement ( 
    case ct of 
        MinCardinality -> "DataMinCardinality"
        MaxCardinality -> "DataMaxCardinality"
        ExactCardinality -> "DataExactCardinality" )
    $ setIRIWithName "DataProperty" dp :
      case mdr of 
          Nothing -> []
          Just dr -> [toDataRange dr]











