{- |
Module      :  $Header$
Description :  CSMOF XMI parser
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.Parser where

import CSMOF.As
import CSMOF.XMLKeywords

import Text.XML.Light
import qualified Data.Map as Map
import qualified Data.Text as Text


parseCSMOF :: Element -> Metamodel
parseCSMOF el = 
  let keyMap = generateKeyMap el
  in
   case checkXMLStructure el of
     True -> let m = Metamodel { metamodelName = parseMetamodelName el
                               , element = parseElements el m keyMap
                               , model = parseModels el m keyMap
                               }
             in m
     False -> err "Not a CSMOF XMI document"	 


checkXMLStructure :: Element -> Bool
checkXMLStructure el = 
  case findElement metamodelK el of
    Nothing -> False
    Just n -> True

parseMetamodelName :: Element -> String
parseMetamodelName el = 
  case lookupAttr metamodelNameK (elAttribs el) of
    Nothing -> err "Metamodel name does not exists"
    Just name -> name


parseElements :: Element -> Metamodel -> Map.Map String String -> [NamedElement]
parseElements el metamodel keyMap = foldr ((:) . (createElement metamodel keyMap)) [] (findChildren elementK el)


createElement :: Metamodel -> Map.Map String String -> Element -> NamedElement
createElement metamodel keyMap elem = 
  let name = parseElementName elem
      typeAtt = parseElementType elem
      isAbs = parseElementIsAbstract elem 
      super = parseElementSuperClass elem
  in
   case typeAtt of
     "CSMOF:DataType" -> createDataType metamodel keyMap name
     "CSMOF:Class" -> createClass metamodel keyMap name isAbs super elem


parseElementName :: Element -> String
parseElementName el = 
  case lookupAttr elementNameK (elAttribs el) of
    Nothing -> err "Element name does not exists"
    Just name -> name


parseElementType :: Element -> String
parseElementType el = 
  case lookupAttr elementTypeK (elAttribs el) of
    Nothing -> err "Element type does not exists"
    Just typ -> typ


parseElementIsAbstract :: Element -> String
parseElementIsAbstract el = 
  case lookupAttr elementIsAbstractK (elAttribs el) of
    Nothing -> "false"
    Just abs -> abs


parseElementSuperClass :: Element -> [String]
parseElementSuperClass el = 
  case lookupAttr elementSuperClassK (elAttribs el) of
    Nothing -> []
    Just subs -> words subs


createDataType :: Metamodel -> Map.Map String String -> String -> NamedElement
createDataType metamodel keyMap name = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DDataType { getDataType = DataType { classSuper = type_X } }
                    }
  in namedElement_X


createClass :: Metamodel -> Map.Map String String -> String -> String -> [String] -> Element -> NamedElement
createClass metamodel keyMap name abs subs el = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DClass { getClass = class_X }
                    }
      class_X = Class { classSuperType = type_X
                      , isAbstract = 
                        case abs of
                          "true" -> True
                          "false" -> False
                      , superClass = foldr ((:) . (linkClass keyMap metamodel)) [] subs
                      , ownedAttribute = foldr ((:) . (createProperty metamodel keyMap)) [] (findChildren ownedAttributeK el)
                      }
  in namedElement_X


createProperty :: Metamodel -> Map.Map String String -> Element -> Property
createProperty metamodel keyMap el = err "TODO"

--ne = NamedElement 
  --                  { namedElementName :: String
    --                , namedElementOwner :: Metamodel
      --              , namedElementSubClasses :: TypeOrTypedElement
        --            }

--TypeOrTypedElement = TType { getType :: Type }
--                        | TTypedElement { getTypeElement :: TypedElement }

--TypedElement 
--                    { typedElementSuper :: NamedElement 
--                    , typedElementType :: Type 
--                    , typedElementSubClasses :: Property
--                    }

	--Property { propertySuper :: TypedElement
--                , multiplicityElement :: MultiplicityElement
--                , opposite :: Maybe Property
--                , propertyClass :: Class
--                }




-------- Model Part

parseModels :: Element -> Metamodel -> Map.Map String String -> [Model]
parseModels el metamodel keyMap = foldr ((:) . (createModel metamodel keyMap)) [] (findChildren modelK el)


createModel :: Metamodel -> Map.Map String String -> Element -> Model
createModel metamodel keyMap el = 
  let model = Model { modelName = parseModelName el
                    , object = parseObjects metamodel model keyMap el
                    , link = [] --TODO
                    , modelType = metamodel
                    }
  in model


parseModelName :: Element -> String
parseModelName el = 
  case lookupAttr modelNameK (elAttribs el) of
    Nothing -> err "Model name does not exists"
    Just name -> name


parseObjects :: Metamodel -> Model -> Map.Map String String -> Element -> [Object]
parseObjects metamodel model keyMap el = foldr ((:) . (createObject metamodel model keyMap)) [] (findChildren objectK el)

createObject :: Metamodel -> Model -> Map.Map String String -> Element -> Object
createObject metamodel model keyMap elem = 
  let name = parseObjectName elem
      typeAtt = parseObjectType elem
  in
	Object { objectName = name
        	, objectType = linkTypeElem keyMap metamodel typeAtt
                , objectOwner = model
                }

parseObjectName :: Element -> String
parseObjectName el = 
  case lookupAttr objectNameK (elAttribs el) of
    Nothing -> err "Object name does not exists"
    Just name -> name

parseObjectType :: Element -> String
parseObjectType el = 
  case lookupAttr objectTypeK (elAttribs el) of
    Nothing -> err "Object type does not exists"
    Just typ -> typ



----- Functions for linking elements searching on of them using it key

linkClass :: Map.Map String String -> Metamodel -> String -> Class
linkClass keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toClass (filter (equalClassName name) (element metamodel))
  in 
   case list of
     [] -> err ("Class not found: " ++ name)
     h : rest -> h


linkObject :: Map.Map String String -> Metamodel -> String -> Object
linkObject keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = filter (equalObjectName name) (object (rightModel keyMap metamodel key))
  in 
   case list of
     [] -> err ("Object not found: " ++ name)
     h : rest -> h


linkTypeElem :: Map.Map String String -> Metamodel -> String -> Type
linkTypeElem keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toType (filter (equalTypeName name) (element metamodel))
  in 
   case list of
     [] -> err ("Class not found: " ++ name)
     h : rest -> h


linkProperty :: Map.Map String String -> Metamodel -> String -> Property
linkProperty keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toProperty (filter (equalPropertyName name) (element metamodel))
  in 
   case list of
     [] -> err ("Class not found: " ++ name)
     h : rest -> h


equalClassName :: String -> NamedElement -> Bool
equalClassName name ne =
  case ne of
    (NamedElement na ow (TType (Type sup (DClass cl)))) -> (namedElementName ne) == name
    otherwise -> False
    
toClass :: NamedElement -> Class
toClass ne =
  case ne of
    (NamedElement na ow (TType (Type sup (DClass cl)))) -> cl
    otherwise -> err ("Wrong cast: " ++ (namedElementName ne))


equalObjectName :: String -> Object -> Bool
equalObjectName name ob = (objectName ob) == name


equalTypeName :: String -> NamedElement -> Bool
equalTypeName name ne =
  case ne of
    (NamedElement na ow (TType ty)) -> (namedElementName ne) == name
    otherwise -> False
    
toType :: NamedElement -> Type
toType ne =
  case ne of
    (NamedElement na ow (TType ty)) -> ty
    otherwise -> err ("Wrong cast: " ++ (namedElementName ne))


equalPropertyName :: String -> NamedElement -> Bool
equalPropertyName name ne =
  case ne of
    (NamedElement na ow (TTypedElement (TypedElement sup typ pro))) -> (namedElementName ne) == name
    otherwise -> False
    
toProperty :: NamedElement -> Property
toProperty ne =
  case ne of
    (NamedElement na ow (TTypedElement (TypedElement sup typ pro))) -> pro
    otherwise -> err ("Wrong cast: " ++ (namedElementName ne))



-- Search for the right model according to the key
rightModel :: Map.Map String String -> Metamodel -> String -> Model
rightModel keyMap metamodel key = head (filter (isModel keyMap key) (model metamodel))

isModel :: Map.Map String String -> String -> Model -> Bool
isModel keyMap key model = (modelName model) == (findElementInMap (getModelKey key) keyMap)

getModelKey :: String -> String
getModelKey key = Text.unpack (Text.dropWhileEnd (/='/') (Text.pack key))
-- head (splitRegex (mkRegex "/@object") key)


findElementInMap :: String -> Map.Map String String -> String
findElementInMap key keyMap =
  let elName = Map.lookup key keyMap
  in 
   case elName of
     Nothing -> err ("Key not found: " ++ key)
     Just name -> name



----- Generates a Key Map for processing references between elements

generateKeyMap :: Element -> Map.Map String String
generateKeyMap el = 
  let modelMap = snd (foldr (createModelKey) (0, Map.empty) (reverse (findChildren modelK el)))
  in snd (foldr (createElementKey) (0, modelMap) (reverse (findChildren elementK el)))


createElementKey :: Element -> (Integer, Map.Map String String) -> (Integer, Map.Map String String)
createElementKey elem (pos,map) = 
  let key = "//@element." ++ (show pos)
      mapElements = Map.insert key (parseElementName elem) map
  in (pos + 1, third (foldr (createChildrenKeys) (key ++ "/@ownedAttribute.", 0, mapElements) (reverse (findChildren ownedAttributeK elem))))


createModelKey :: Element -> (Integer, Map.Map String String) -> (Integer, Map.Map String String)
createModelKey elem (pos,map) = 
  let key = "//@model." ++ (show pos)
      mapModel = Map.insert key (parseModelName elem) map
  in (pos + 1, third (foldr (createChildrenKeys) (key ++ "/@object.", 0, mapModel) (reverse (findChildren objectK elem))))


createChildrenKeys :: Element -> (String, Integer, Map.Map String String) -> (String, Integer, Map.Map String String)
createChildrenKeys elem (keySup, pos, map) = 
  let key = keySup ++ (show pos)
  in (keySup, pos + 1, Map.insert key (parseObjectName elem) map)


third :: (String, Integer, Map.Map String String) -> Map.Map String String
third (a, b, c) = c



----- Auxiliary Functions

-- | error messages for the parser
err :: String -> t
err s = error $ "XML parser: " ++ s

