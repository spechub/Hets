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
     True -> let m = Metamodel { metamodelName = parseStringAttribute el metamodelNameK
                               , element = parseElements el m keyMap
                               , model = parseModels el m keyMap
                               }
             in m
     False -> err "Not a CSMOF XMI document"

checkXMLStructure :: Element -> Bool
checkXMLStructure el = 
  case findElement metamodelK el of
    Nothing -> False
    Just _ -> True


parseElements :: Element -> Metamodel -> Map.Map String String -> [NamedElement]
parseElements el metamodel keyMap = foldr ((++) . (createElement metamodel keyMap)) [] (findChildren elementK el)

-- Returns a list of elements, in the case of a class, the class and its properties
createElement :: Metamodel -> Map.Map String String -> Element -> [NamedElement]
createElement metamodel keyMap eleme = 
  let name = parseStringAttribute eleme elementNameK
      typeAtt = parseStringAttribute eleme elementTypeK
      isAbs = parseBoolAttribute eleme elementIsAbstractK
      super = parseElementSuperClass eleme
  in
   case typeAtt of
     "CSMOF:DataType" -> createDataType metamodel keyMap name
     _ -> createClass metamodel keyMap name isAbs super eleme -- It is a class


parseElementSuperClass :: Element -> [String]
parseElementSuperClass el = 
  case lookupAttr elementSuperClassK (elAttribs el) of
    Nothing -> []
    Just subs -> words subs


createDataType :: Metamodel -> Map.Map String String -> String -> [NamedElement]
createDataType metamodel _ name = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DDataType { getDataType = DataType { classSuper = type_X } }
                    }
  -- there is only one element
  in (namedElement_X : [])


createClass :: Metamodel -> Map.Map String String -> String -> Bool -> [String] -> Element -> [NamedElement]
createClass metamodel keyMap name abst subs el = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DClass { getClass = class_X }
                    }
      class_X = Class { classSuperType = type_X
                      , isAbstract = abst
                      , superClass = foldr ((:) . (linkClass keyMap metamodel)) [] subs
                      , ownedAttribute = ownedAttributes
                      }
      ownedAttributes = foldr ((:) . (createProperty metamodel keyMap class_X)) [] (findChildren ownedAttributeK el)
  -- there is the class and every property inside it
  in (namedElement_X : (map (typedElementSuper . propertySuper) ownedAttributes))


createProperty :: Metamodel -> Map.Map String String -> Class -> Element -> Property
createProperty metamodel keyMap cla el = 
  let lowe = parseIntegerAttribute el ownedAttributeLowerK
      uppe = parseIntegerAttribute el ownedAttributeUpperK
      name = parseStringAttribute el ownedAttributeNameK
      typeEl = parsePropertyType keyMap metamodel el
      opp = parsePropertyOpposite keyMap metamodel el
      namedElement = NamedElement { namedElementName = name
                                  , namedElementOwner = metamodel
                                  , namedElementSubClasses = TTypedElement { getTypeElement = typedElement }
                                  }
      typedElement = TypedElement { typedElementSuper = namedElement
                                  , typedElementType = typeEl
                                  , typedElementSubClasses = property
                                  }
      property = Property { propertySuper = typedElement
                          , multiplicityElement = MultiplicityElement { lower = lowe
                                                                      , upper = uppe
                                                                      , multiplicityElementSubClasses = property
                                                                      }
                          , opposite = opp
                          , propertyClass = cla
                          }
  in  property
      

parsePropertyType :: Map.Map String String -> Metamodel -> Element -> Type
parsePropertyType keyMap metamodel el = 
  case lookupAttr ownedAttributeTypeK (elAttribs el) of
    Nothing -> err "Property type does not exists"
    Just typ -> linkTypeElem keyMap metamodel typ


parsePropertyOpposite :: Map.Map String String -> Metamodel -> Element -> Maybe Property
parsePropertyOpposite keyMap metamodel el = 
  case lookupAttr ownedAttributeOppositeK (elAttribs el) of
    Nothing -> Nothing
    Just opp -> Just (linkProperty keyMap metamodel opp)



-------- Model Part

parseModels :: Element -> Metamodel -> Map.Map String String -> [Model]
parseModels el metamodel keyMap = foldr ((:) . (createModel metamodel keyMap)) [] (findChildren modelK el)


createModel :: Metamodel -> Map.Map String String -> Element -> Model
createModel metamodel keyMap el = 
  let mode = Model { modelName = parseStringAttribute el modelNameK
                   , object = parseObjects metamodel mode keyMap el
                   , link = parseLinks metamodel mode keyMap el
                   , modelType = metamodel
                   }
  in mode


parseObjects :: Metamodel -> Model -> Map.Map String String -> Element -> [Object]
parseObjects metamodel mode keyMap el = foldr ((:) . (createObject metamodel mode keyMap)) [] (findChildren objectK el)

createObject :: Metamodel -> Model -> Map.Map String String -> Element -> Object
createObject metamodel mode keyMap eleme = 
  let name = parseStringAttribute eleme objectNameK
      typeAtt = parseStringAttribute eleme objectTypeK
  in Object { objectName = name
            , objectType = linkTypeElem keyMap metamodel typeAtt
            , objectOwner = mode
            }


parseLinks :: Metamodel -> Model -> Map.Map String String -> Element -> [Link]
parseLinks metamodel mode keyMap el = foldr ((:) . (createLink metamodel mode keyMap)) [] (findChildren linkK el)

createLink :: Metamodel -> Model -> Map.Map String String -> Element -> Link
createLink metamodel mode keyMap eleme = 
  let typ = parseStringAttribute eleme linkTypeK
      sour = parseStringAttribute eleme linkSourceK
      targ = parseStringAttribute eleme linkTargetK
  in Link { linkType = linkProperty keyMap metamodel typ
          , source = linkObject keyMap metamodel sour
          , target = linkObject keyMap metamodel targ
          , linkOwner = mode
          }


parseStringAttribute :: Element -> QName -> String
parseStringAttribute el key = 
  case lookupAttr key (elAttribs el) of
    Nothing -> err ("Attribute does not exists: " ++ (show key))
    Just typ -> typ

parseIntegerAttribute :: Element -> QName -> Integer
parseIntegerAttribute el key = 
  case lookupAttr key (elAttribs el) of
    Nothing -> 1
    Just low -> read low::Integer

parseBoolAttribute :: Element -> QName -> Bool
parseBoolAttribute el key = 
  case lookupAttr key (elAttribs el) of
    Nothing -> False
    Just abst -> case abst of
                  "true" -> True
                  _ -> False
                  



----- Functions for linking elements searching on of them using it key

linkClass :: Map.Map String String -> Metamodel -> String -> Class
linkClass keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toClass (filter (equalClassName name) (element metamodel))
  in 
   case list of
     [] -> err ("Class not found: " ++ name)
     h : _ -> h


linkObject :: Map.Map String String -> Metamodel -> String -> Object
linkObject keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = filter (equalObjectName name) (object (rightModel keyMap metamodel key))
  in 
   case list of
     [] -> err ("Object not found: " ++ name)
     h : _ -> h


linkTypeElem :: Map.Map String String -> Metamodel -> String -> Type
linkTypeElem keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toType (filter (equalTypeName name) (element metamodel))
  in 
   case list of
     [] -> err ("Type not found: " ++ name)
     h : _ -> h


linkProperty :: Map.Map String String -> Metamodel -> String -> Property
linkProperty keyMap metamodel key = 
  let name = findElementInMap key keyMap
      list = map toProperty (filter (equalPropertyName name) (element metamodel))
  in 
   case list of
     [] -> err ("Property not found: " ++ name)
     h : _ -> h


equalClassName :: String -> NamedElement -> Bool
equalClassName name ne =
  case ne of
    (NamedElement _ _ (TType (Type _ (DClass _)))) -> (namedElementName ne) == name
    _ -> False
    
toClass :: NamedElement -> Class
toClass ne =
  case ne of
    (NamedElement _ _ (TType (Type _ (DClass cl)))) -> cl
    _ -> err ("Wrong cast: " ++ (namedElementName ne))


equalObjectName :: String -> Object -> Bool
equalObjectName name ob = (objectName ob) == name


equalTypeName :: String -> NamedElement -> Bool
equalTypeName name ne =
  case ne of
    (NamedElement _ _ (TType _)) -> (namedElementName ne) == name
    _ -> False
    
toType :: NamedElement -> Type
toType ne =
  case ne of
    (NamedElement _ _ (TType ty)) -> ty
    _ -> err ("Wrong cast: " ++ (namedElementName ne))


equalPropertyName :: String -> NamedElement -> Bool
equalPropertyName name ne =
  case ne of
    (NamedElement _ _ (TTypedElement (TypedElement _ _ _))) -> (namedElementName ne) == name
    _ -> False
    
toProperty :: NamedElement -> Property
toProperty ne =
  case ne of
    (NamedElement _ _ (TTypedElement (TypedElement _ _ pro))) -> pro
    _ -> err ("Wrong cast: " ++ (namedElementName ne))



-- Search for the right model according to the key
rightModel :: Map.Map String String -> Metamodel -> String -> Model
rightModel keyMap metamodel key = head (filter (isModel keyMap key) (model metamodel))

isModel :: Map.Map String String -> String -> Model -> Bool
isModel keyMap key mode = (modelName mode) == (findElementInMap (getModelKey key) keyMap)

getModelKey :: String -> String
getModelKey key = Text.unpack (Text.dropWhileEnd (/='/') (Text.pack key))



findElementInMap :: String -> Map.Map String String -> String
findElementInMap key keyMap =
  let elNam = Map.lookup key keyMap
  in 
   case elNam of
     Nothing -> err ("Key not found: " ++ key)
     Just name -> name



----- Generates a Key Map for processing references between elements

generateKeyMap :: Element -> Map.Map String String
generateKeyMap el = 
  let modelMap = snd (foldr (createModelKey) (0, Map.empty) (reverse (findChildren modelK el)))
  in snd (foldr (createElementKey) (0, modelMap) (reverse (findChildren elementK el)))


createElementKey :: Element -> (Integer, Map.Map String String) -> (Integer, Map.Map String String)
createElementKey eleme (pos,mapp) = 
  let key = "//@element." ++ (show pos)
      mapElements = Map.insert key (parseStringAttribute eleme elementNameK) mapp
  in (pos + 1, third (foldr (createChildrenKeys) (key ++ "/@ownedAttribute.", 0, mapElements) (reverse (findChildren ownedAttributeK eleme))))


createModelKey :: Element -> (Integer, Map.Map String String) -> (Integer, Map.Map String String)
createModelKey eleme (pos,mapp) = 
  let key = "//@model." ++ (show pos)
      mapModel = Map.insert (key ++ "/") (parseStringAttribute eleme modelNameK) mapp
  in (pos + 1, third (foldr (createChildrenKeys) (key ++ "/@object.", 0, mapModel) (reverse (findChildren objectK eleme))))


createChildrenKeys :: Element -> (String, Integer, Map.Map String String) -> (String, Integer, Map.Map String String)
createChildrenKeys eleme (keySup, pos, mapp) = 
  let key = keySup ++ (show pos)
  in (keySup, pos + 1, Map.insert key (parseStringAttribute eleme objectNameK) mapp)


third :: (String, Integer, Map.Map String String) -> Map.Map String String
third (_, _, c) = c



----- Auxiliary Functions

-- | error messages for the parser
err :: String -> t
err s = error $ "XML parser: " ++ s

