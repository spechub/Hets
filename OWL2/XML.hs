module OWL2.XML where

import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS
import Common.Lexer

entityList :: [String]
entityList = ["Class", "Datatype", "NamedIndividual",
    "ObjectProperty", "DataProperty", "AnnotationProperty"]

isEntity :: Text.XML.Light.QName -> Bool
isEntity (QName {qName = qn}) = qn `elem` entityList

isSmth :: String -> Text.XML.Light.QName -> Bool
isSmth s (QName {qName = qn}) = qn == s

getEntityType :: String -> EntityType
getEntityType ty = case ty of
    "Class" -> Class
    "Datatype" -> Datatype
    "NamedIndividual" -> NamedIndividual
    "ObjectProperty" -> ObjectProperty
    "DataProperty" -> DataProperty
    "AnnotationProperty" -> AnnotationProperty
    _ -> error "not entity type"

getIRI :: Element -> OWL2.AS.QName
getIRI (Element {elAttribs = a}) =
        let Attr {attrVal = iri} = head a
        in mkQName iri

getInt :: Element -> Int
getInt (Element {elAttribs = a}) =
        let Attr {attrVal = int} = head a
        in value 10 int


getName :: Element -> String
getName (Element {elName = QName {qName = n}}) = n

toEntity :: Element -> Entity
toEntity e = Entity (getEntityType $ getName e) (getIRI e)

getEntity :: Element -> Entity
getEntity e = toEntity $ fromJust $ filterElementName isEntity e

getDeclaration :: Element -> Frame
getDeclaration e =
   let ent = fromJust $ filterChildName isEntity e
       ans = getAllAnnos e
   in Frame (Right $ toEntity ent) [AnnFrameBit ans AnnotationFrameBit]

getDeclarations :: Element -> [Frame]
getDeclarations e =
   let dcl = filterElementsName (isSmth "Declaration") e
   in map getDeclaration dcl

isPlainLiteral :: String -> Bool
isPlainLiteral s = "PlainLiteral" == drop (length s - 12) s

getLiteral :: Element -> Literal
getLiteral e = let lit = fromJust $ filterElementName (isSmth "Literal") e
                   lf = strContent e
                   dt = fromJust $ findAttrBy (isSmth "datatypeIRI") lit
               in
                  case findAttrBy (isSmth "lang") lit of
                    Just lang -> Literal lf (Untyped $ Just lang)
                    Nothing -> if isPlainLiteral dt then
                                  Literal lf (Untyped Nothing)
                                else Literal lf (Typed $ mkQName dt)

getValue :: Element -> AnnotationValue
getValue e = let lit = filterElementName (isSmth "Literal") e
                 val = strContent e
             in case lit of
                  Nothing -> AnnValue $ mkQName val
                  Just _ -> AnnValLit $ getLiteral e

filterElem :: String -> Element -> [Element]
filterElem s = filterElementsName (isSmth s)

getAnnotation :: Element -> Annotation
getAnnotation e =
     let hd = filterChildrenName (isSmth "Annotation") e
         ap = filterElem "AnnotationProperty" e
         av = filterElem "Literal" e ++ filterElem "IRI" e
     in
          Annotation (getAnnotations hd)
              (getIRI $ head ap) (getValue $ head av)

getAnnotations :: [Element] -> [Annotation]
getAnnotations e = map getAnnotation $ concatMap
            (filterElementsName (isSmth "Annotation")) e

getAllAnnos :: Element -> [Annotation]
getAllAnnos e = map getAnnotation
            $ filterElementsName (isSmth "Annotation") e

 -- still need to cancel double inverses
getObjProp :: Element -> ObjectPropertyExpression
getObjProp e = case filterElementName (isSmth "ObjectInverseOf") e of
                  Nothing -> ObjectProp $ getIRI e
                  Just _ -> ObjectInverseOf $ getObjProp $ head $ elChildren e

getFacetValuePair :: Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair e = (getIRI e, getLiteral $ head $ elChildren e)

getDataRange :: Element -> DataRange
getDataRange e = case getName e of
    "Datatype" -> DataType (getIRI e) []
    "DatatypeRestriction" ->
        let dt = getIRI $ fromJust $ filterChildName (isSmth "Datatype") e
            fvp = map getFacetValuePair
               $ filterChildrenName (isSmth "FacetRestriction") e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf
            $ getDataRange $ head $ elChildren e
    "DataOneOf" -> DataOneOf
            $ map getLiteral $ filterChildrenName (isSmth "Literal") e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map getDataRange $ elChildren e
    "DataUnionOf" -> DataJunction UnionOf
            $ map getDataRange $ elChildren e
    _ -> error "XML parser: not data range"

getClassExpression :: Element -> ClassExpression
getClassExpression e = case getName e of
    "Class" -> Expression $ getIRI e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map getClassExpression $ elChildren e
    "ObjectUnionOf" -> ObjectJunction UnionOf
            $ map getClassExpression $ elChildren e
    "ObjectComplementOf" -> ObjectComplementOf
            $ getClassExpression $ head $ elChildren e
    "ObjectOneOf" -> ObjectOneOf
            $ map getIRI $ elChildren e
    "ObjectSomeValuesFrom" -> let ch = elChildren e in
        ObjectValuesFrom SomeValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectAllValuesFrom" -> let ch = elChildren e in
        ObjectValuesFrom AllValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectHasValue" -> let ch = elChildren e in
        ObjectHasValue (getObjProp $ head ch) (getIRI $ last ch)
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp $ head $ elChildren e
    "ObjectMinCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectMaxCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectExactCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch) Nothing
    "DataSomeValuesFrom" -> 
        let ch = elChildren e 
            dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom SomeValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataAllValuesFrom" -> 
        let ch = elChildren e 
            dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom AllValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataHasValue" -> let ch = elChildren e in
        DataHasValue (getIRI $ head ch) (getLiteral $ last ch)
    "DataMinCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataMaxCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataExactCardinality" -> let ch = elChildren e in
        if length ch == 2 then
          DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch) Nothing
    _ -> error "XML parser: not ClassExpression"









