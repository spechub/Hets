module OWL2.XML where

import Common.DocUtils
import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS

entityList :: [String]
entityList = ["Class", "Datatype", "NamedIndividual", 
    "ObjectProperty", "DataProperty", "AnnotationProperty"]

isEntity :: Text.XML.Light.QName -> Bool
isEntity (QName {qName = qn}) = elem qn entityList

isDecl :: Text.XML.Light.QName -> Bool
isDecl (QName {qName = qn}) = qn == "Declaration"

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
getDeclarations e = concatMap getEntities $ catMaybes $ map (filterChildName isEntity) 
            $ filterElementsName isDecl e





