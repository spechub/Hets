module FreeCAD.Translator

where
import FreeCAD.As
import Text.XML.Light
import Data.Maybe
import Data.Set as Set



--constants used to find the appropriate subtree in the XML file:
objListQName::QName
objListQName = makeQName "ObjectData"
    --qualified name of the element which contains the list of objects
    --with their properties
objQName::QName
objQName = makeQName "Object"
    --qualified name for the element which represents an object
    
    
objListEl:: Element -> Maybe Element
objListEl mbel = findChild objListQName mbel 
    --the xml element containing all objects and their data:: Element
objList:: Element -> [Element]
objList mbel= findChildren objQName (fromJust (objListEl mbel))
    --list of xml elements containing data for each object:: [Element]
            

firstThree :: String -> String
firstThree x = take 3 x

makeQName:: String -> QName
makeQName s = QName s Nothing Nothing

getName:: Element -> String
getName el = fromJust (findAttr (makeQName "name") el)
hasName:: String -> Element -> Bool
hasName s el = (getName el == s)

childByName:: String -> Element -> Element
childByName s el = fromJust (findChild (makeQName s) el)
childByNameAttr:: String -> Element -> Element
childByNameAttr s el = fromJust (filterChild(hasName s) el)

-- a Set constant -- TODO: find signature
setBaseObjs:: Set.Set [Char]
setBaseObjs = fromList["Box", "Sph", "Cyl", "Con", "Tor", "Cir", "Rec"]

isBaseObject:: Element -> Bool
isBaseObject el = member (firstThree (getName el)) setBaseObjs  
    -- identify (by its name) whether an object is simpe or extended
    -- returns true if it is a base object and false otherwise
                
                 
--used in order to identify the object constructor from the name

getObject:: Element -> FreeCAD.As.NamedObject
getObject el | tn == "Box" = makeb el tn
             | tn == "Sph" = makeb el tn
             | tn == "Cyl" = makeb el tn
             | tn == "Con" = makeb el tn
             | tn == "Tor" = makeb el tn
             | tn == "Cir" = makeb el tn
             | tn == "Rec" = EmptyObject
             | tn == "Lin" = EmptyObject
             | tn == "Cut" = makex el tn
             | tn == "Com" = makex el tn 
             | tn == "Fus" = makex el tn
             | tn == "Sec" = makex el tn
			 | tn == "Ext" = EmptyObject
            where 
              tn = firstThree(getName el) 
              makeb el tn = NamedObject (getName el) (PlacedObject (findPlacement elc) (BaseObject (bbuild tn el)))
              makex el tn = NamedObject (getName el) (PlacedObject (findPlacement elc) (buildex tn el))
              bbuild tn el | tn == "Box" = Box (findFloat "Height" elc) (findFloat "Width" elc) (findFloat "Length" elc)
                           | tn == "Sph" = Sphere (findFloat "Angle1" elc) (findFloat "Angle2" elc) (findFloat "Angle3" elc) (findFloat "Radius" elc)
                           | tn == "Cyl" = Cylinder (findFloat "Angle" elc) (findFloat "Height" elc) (findFloat "Radius" elc)
                           | tn == "Con" = Cone (findFloat "Angle" elc) (findFloat "Radius1" elc) (findFloat "Radius2" elc) (findFloat "Height" elc)
                           | tn == "Tor" = Torus (findFloat "Angle1" elc) (findFloat "Angle2" elc) (findFloat "Angle3" elc) (findFloat "Radius1" elc) (findFloat "Radius2" elc)
                           | tn == "Cir" = Circle (findFloat "StartAngle" elc) (findFloat "EndAngle" elc) (findFloat "Radius" elc)
                       --  | tn == "Rec" = Rectangle TODO
                       --  | tn == "Lin" = Line TODO
              buildex tn el | tn == "Cut" = Cut (findRef "Base" elc) (findRef "Tool" elc)
                            | tn == "Com" = Common (findRef "Base" elc) (findRef "Tool" elc)
                            | tn == "Fus" = Fusion (findRef "Base" elc) (findRef "Tool" elc)
                            | tn == "Sec" = Section (findRef "Base" elc) (findRef "Tool" elc)
              elc = child el



getVal:: String -> Element -> String
getVal s el = fromJust (findAttr (makeQName s) el)

getFloatVal:: Element -> String
getFloatVal el = getVal "value" el2
    where
        el2 = childByName "Float" el

getPlacementVals::Element -> (String, String, String, String, String, String, String)
getPlacementVals el = (m "Px", m "Py", m "Pz", m "Q0", m "Q1", m "Q2", m "Q3")
    where
        m s = getVal s el2
        el2 = childByName "PropertyPlacement" el
getLinkVal:: Element -> String
getLinkVal el = getVal "value" el2
    where
        el2 = childByName "Link" el

findFloat:: String -> Element -> Double
findFloat s el = read (getFloatVal el2)
    where
        el2 = childByNameAttr s el
findPlacement::Element -> FreeCAD.As.Placement        
findPlacement el = Placement (Vector3 a b c) (Vector4 d e f g)
	where
        (sa, sb, sc, sd, se, sf, sg) = getPlacementVals el2
        a = read sa
        b = read sb
        c = read sc
        d = read sd
        e = read se
        f = read sf
        g = read sg
        el2 = childByNameAttr "Placement" el

findRef::String -> Element -> FreeCAD.As.ExtendedObject        
findRef s el = Ref (getLinkVal el2)
    where 
        el2 = childByNameAttr s el

child:: Element -> Element
child el = head(elChildren el)

--Facade function that translates the parsed XML document into Haskell-FreeCAD datatype

translate:: Element -> Document
translate baseElement = document
    where
	objects = objList baseElement
	document = Prelude.map getObject objects

