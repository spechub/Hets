module FreeCAD.Parser 
    where

import System.IO
import Text.XML.Light
import Data.Maybe
import FreeCAD.Translater


--the IO part of the program:--
processFile = do
  xmlInput <-readFile "input.xml"
  let parsed = parseXMLDoc xmlInput
  let out = output parsed
  putStrLn out
-------------------------------


--wrapper of the parser--------
--parse a = process (parseXML a)
-------------------------------


--find the node containing the object names
isObectList :: QName -> Bool

iObjectList a = if (qName a) == "ObjectData" then true else false
objectsList = filterChildName isObjectList xmlInput

getObjectName :: Element -> String

store [] = []
store [elem:elemList] = (store elem) : (store elemList)
store (Elem element) = storeElement element
storeElement x | qName (elName x) == "ObjectData" = store elContent x
               | qName (elName x) == "Object" = storeObject x
               
               
storeObject x | findName x != "" = let
                                     name = findName x
                                   in 
                                     NamedObject (name) PlacedObject (Palcement (Object (findType (name, x))) ) 

nameFromAttributes [] = ""
nameFromAttributes [at:attrs] if qName (attrKey at )== "name" 
                                then attrVal at
                                else nameFromAttributes [attrs]

findName x = nameFromAttributes elAttribs x

findType (findName x, x) | =


output x = show (elName x)
