module FreeCAD.Translator

where
import Text.XML.Light
import FreeCAD.As
import Maybe
import Data.Set

{-
translate:: Maybe Element -> Document

isBaseObject:: Element -> Bool

getObject:: Element -> NamedObject
getBaseObject:: Element -> BaseObject
getExtendedObject:: Element -> ExtendedObject
getPlacement:: Element -> Placement
getName:: Element -> String
getProperty:: Element -> String -> Double
-}



--TODO translate mbel -- wrapper for the module


setBaseObjs = fromList ["Box","Sph","Cyl","Con","Tor","Cir","Rec"]

objListQName = makeQName "ObjectData"
    --qualified name of the element which contains the list of objects
    --with their properties
objQName = makeQName "Object"
    --qualified name for the element which represents an object
objListEl mbel = findChild objListQName mbel 
    --the xml element containing all objects and their data:: Element
objList mbel= findChildren objQName (fromJust (objListEl mbel))
    --list of xml elements containing data for each object:: [Element]
            

firstThree :: String -> String
firstThree x = take 3 x


getName el = fromJust (findAttr (makeQName "name") el)

makeQName:: String -> QName
makeQName s = QName s Nothing Nothing

isBaseObject:: Element -> Bool
isBaseObject el = member (firstThree (getName el)) setBaseObjs  
    -- identify (by its name) whether an object is simpe or extended
    -- returns true if it is a base object and false otherwise
                
                 
--used in order to identify the object constructor from the name





--TODO returns constructor and properties for base objects from element
exConsNprops el = error "TODO"--TODO returns constructor and properties for extended objects from element

findPlacement el = error "TODO"

getObject el | tn == "Box" = makeb el tn
             | tn == "Sph" = makeb el tn
             | tn == "Cyl" = makeb el tn
             | tn == "Con" = makeb el tn
             | tn == "Tor" = makeb el tn
             | tn == "Cir" = makeb el tn
             | tn == "Rec" = makeb el tn
             | tn == "Cut" = makex el tn
             | tn == "Com" = makex el tn 
             | tn == "Fus" = makex el tn
             | tn == "Sec" = makex el tn
            where 
              tn = firstThree(getName el) 
              makeb el tn = NamedObject (getName el) (PlacedObject (findPlacement el) (BaseObject (bbuild tn el)))
              makex el tn = NamedObject (getName el) (PlacedObject (findPlacement el) (buildex tn el))
              bbuild = error "TODO"
              buildex = error "TODO"
    
    
