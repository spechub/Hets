module OWL2.XML where

import Common.DocUtils
import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS

import Data.List

entityList :: [String]
entityList = ["Class", "Datatype", "NamedIndividual", 
    "ObjectProperty", "DataProperty", "AnnotationProperty"]

isEntity :: Text.XML.Light.QName -> Bool
isEntity (QName {qName = qn}) = elem qn entityList

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

getIRI :: Element -> OWL2.AS.QName
getIRI (Element {elAttribs = a}) = let Attr {attrVal = iri} = head a 
        in mkQName iri

getName :: Element -> String
getName (Element {elName = QName {qName = n}}) = n

toEntity :: Element -> Entity
toEntity e = Entity (getEntityType $ getName e) (getIRI e)

getEntities :: Element -> [Entity]
getEntities e = map toEntity $ filterElementsName isEntity e

getDeclarations :: Element -> [Entity]
getDeclarations e = concatMap getEntities $ catMaybes 
      $ map (filterChildName isEntity) 
            $ filterElementsName (isSmth "Declaration") e

isPlainLiteral :: String -> Bool
isPlainLiteral s = "PlainLiteral" == drop (length s - 12) s

getLiteral :: Element -> Literal
getLiteral e = let lit = fromJust $ filterElementName (isSmth "Literal") e 
                   lf = strContent e
                   dt = fromJust $ findAttrBy (isSmth "datatypeIRI") lit
               in
                  case (findAttrBy (isSmth "lang") lit) of
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
filterElem s e = filterElementsName (isSmth s) e 

getAnnotation :: Element -> Annotation
getAnnotation e = 
     let hd = filterChildrenName (isSmth "Annotation") e 
         ap = filterElem "AnnotationProperty" e 
         av = filterElem "Literal" e ++ filterElem "IRI" e
     in 
          Annotation (getAnnotations hd) (getIRI $ head ap) (getValue $ head av)

getAnnotations :: [Element] -> [Annotation]
getAnnotations e = map getAnnotation $ concatMap (filterElementsName (isSmth "Annotation")) e

getAllAnnos :: Element -> [Annotation]
getAllAnnos e = map getAnnotation $ filterElementsName (isSmth "Annotation") e







