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

makeQName:: String -> QName
makeQName s = QName s Nothing Nothing


getName el = fromJust (findAttr (makeQName "name") el)
hasName s el = (getName el == s)

childByName s el = fromJust (findChild (makeQName s) el)
childByNameAttr s el = fromJust (filterChild(hasName s) el)

setBaseObjs = fromList["Box", "Sph", "Cyl", "Con", "Tor", "Cir", "Rec"]

isBaseObject:: Element -> Bool
isBaseObject el = member (firstThree (getName el)) setBaseObjs  
    -- identify (by its name) whether an object is simpe or extended
    -- returns true if it is a base object and false otherwise
                
                 
--used in order to identify the object constructor from the name


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
              bbuild tn el | tn == "Box" = Box (findFloat "Height" el) (findFloat "Width" el) (findFloat "Length" el)
                           | tn == "Sph" = Sphere (findFloat "Angle1" el) (findFloat "Angle2" el) (findFloat "Angle3" el) (findFloat "Radius" el)
                           | tn == "Cyl" = Cylinder (findFloat "Angle" el) (findFloat "Height" el) (findFloat "Radius" el)
                           | tn == "Con" = Cone (findFloat "Angle" el) (findFloat "Radius1" el) (findFloat "Radius2" el) (findFloat "Height" el)
                           | tn == "Tor" = Torus (findFloat "Angle1" el) (findFloat "Angle2" el) (findFloat "Angle3" el) (findFloat "Radius1" el) (findFloat "Radius2" el)
                           | tn == "Cir" = Circle (findFloat "StartAngle" el) (findFloat "EndAngle" el) (findFloat "Radius" el)
                           | tn == "Rec" = Rectangle (findFloat "Height" el) (findFloat "Length" el)
              buildex tn el | tn == "Cut" = Cut (findRef "Base" el) (findRef "Tool" el)
                            | tn == "Com" = Common (findRef "Base" el) (findRef "Tool" el)
                            | tn == "Fus" = Fusion (findRef "Base" el) (findRef "Tool" el)
                            | tn == "Sec" = Section (findRef "Base" el) (findRef "Tool" el)




getVal s el = fromJust (findAttr (makeQName s) el)


getFloatVal el = getVal "value" el2
    where
        el2 = childByName "Float" el

getPlacementVals el = (m "Px", m "Py", m "Pz", m "Q1", m "Q2", m "Q3")
    where
        m s = getVal s el2
        el2 = childByName "PropertyPlacement" el

getLinkVal el = getVal "value" el2
    where
        el2 = childByName "Link" el
        
findFloat s el = getFloatVal el2
    where
        el2 = childByNameAttr s el
        
findPlacement el = Placement (Vector a b c) (Vector d e f)
    where
        (a, b, c, d, e, f) = getPlacementVals el2
        el2 = childByNameAttr "Placement"
        
findRef s el = getLinkVal el2
    where 
        el2 = childByNameAttr s el
    
