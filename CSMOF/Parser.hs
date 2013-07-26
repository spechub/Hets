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


parseCSMOF :: Element -> Metamodel
parseCSMOF el = 
  case checkXMLStructure el of
    True -> let m = Metamodel { metamodelName = parseMetamodelName el
                              , element = parseElements el m
                              , model = parseModels el m
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


parseElements :: Element -> Metamodel -> [NamedElement]
parseElements el metamodel = foldr ((:) . (createElement metamodel) . elAttribs) [] (findChildren elementK el)

createElement :: Metamodel -> [Attr] -> NamedElement
createElement metamodel att = 
  let name = lookupAttr elementNameK att
      typeAtt = lookupAttr elementTypeK att
      isAbs = lookupAttr elementIsAbstractK att
  in
   case name of
     Nothing -> err "Element name does not exists"
     Just na -> 
       case typeAtt of
         Nothing -> err "Element type does not exists"
         Just elT -> 
           case elT of
             "CSMOF:DataType" -> createDataType metamodel na
             "CSMOF:Class" -> 
               case isAbs of
                 Nothing -> createClass metamodel na "false"
                 Just abs -> createClass metamodel na abs


createDataType :: Metamodel -> String -> NamedElement
createDataType metamodel name = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DDataType { getDataType = DataType { classSuper = type_X } }
                    }
  in namedElement_X


createClass :: Metamodel -> String -> String -> NamedElement
createClass metamodel name abs = 
  let namedElement_X = NamedElement { namedElementName = name
                                    , namedElementOwner = metamodel
                                    , namedElementSubClasses = TType { getType = type_X }
                                    }
      type_X = Type { typeSuper = namedElement_X
                    , typeSubClasses = DClass { getClass = class_X }
                    }
      class_X = Class { classSuperType = type_X
                      , isAbstract = case abs of
                                       "true" -> True
                                       "false" -> False
                      , superClass = [] -- TODO
                      , ownedAttribute = [] -- TODO
                      }
  in namedElement_X


parseModels :: Element -> Metamodel -> [Model]
parseModels el metamodel = foldr ((:) . (createModel metamodel)) [] (findChildren modelK el)


createModel :: Metamodel -> Element -> Model
createModel metamodel el = let model = Model { modelName = parseModelName el
                		    , object = parseObjects el metamodel model
		                    , link = [] --TODO
		                    , modelType = metamodel
                    		}
			in model


parseModelName :: Element -> String
parseModelName el = 
  case lookupAttr modelNameK (elAttribs el) of
    Nothing -> err "Model name does not exists"
    Just name -> name


parseObjects :: Element -> Metamodel -> Model -> [Object]
parseObjects el metamodel model = foldr ((:) . (createObject metamodel model) . elAttribs) [] (findChildren objectK el)

createObject :: Metamodel -> Model -> [Attr] -> Object
createObject metamodel model att = 
  let name = lookupAttr objectNameK att
      typeAtt = lookupAttr objectTypeK att
  in
   case name of
     Nothing -> err "Object name does not exists"
     Just na -> 
       case typeAtt of
         Nothing -> err "Object type does not exists"
         Just elT -> err "Object type does not exists" --Object { objectName = na
	               --     , objectType = Type (object model)
                         --   , objectOwner = model
                           -- }


----- Auxiliary Functions

-- | error messages for the parser
err :: String -> t
err s = error $ "XML parser: " ++ s

