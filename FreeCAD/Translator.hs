{- |
Module      :  $Header$
Description :  The main part of the module. Here the parsing, translation of the
               input xml is handled, as well as the I/O.
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Declaration of the abstract datatypes of FreeCAD terms
-}
module FreeCAD.Translator where
import FreeCAD.As
import Text.XML.Light
import Data.Maybe
import Data.Set as Set
import FreeCAD.Brep
import System.Directory
import System.Process
import FreeCAD.PrintAs()


processFile :: FilePath -> IO Document
--unzips the freecad archive, reads the main "Document.xml" file and gives control
--to (translate :: Element -> IO Document) function to interpret the xml data
processFile fp = do
  tempDir <- getTemporaryDirectory
--  putStrLn $ show $ ["unzip", "-of", fp, "-d", tempDir]
  readProcess "unzip" ["-o", fp, "-d", tempDir] []
  xmlInput <-readFile (concat[tempDir, "/Document.xml"])
  let parsed = parseXMLDoc xmlInput
  translate $ fromJust parsed
  --putStrLn (show $printDoc out)
  --putStrLn (show out)
------------------------




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
firstThree s = take 3 s

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

getObject:: Element -> IO NamedObject
getObject el | tn == "Box" = mkBaseObject $ getBox elc
             | tn == "Sph" = mkBaseObject $ getSph elc
             | tn == "Cyl" = mkBaseObject $ getCyl elc
             | tn == "Con" = mkBaseObject $ getCon elc
             | tn == "Tor" = mkBaseObject $ getTor elc
             | tn == "Cir" = mkBaseObject $ getCir elc
             | tn == "Rec" = mkRectangle el
             | tn == "Lin" = mkLine el --TODO
             | tn == "Cut" = mkObject $ getCut elc
             | tn == "Com" = mkObject $ getCom elc
             | tn == "Fus" = mkObject $ getFus elc
             | tn == "Sec" = mkObject $ getSec elc
             | tn == "Ext" = mkObject $ getExt elc
    where
      tn = firstThree(getName el)
      mkObject = return . NamedObject (getName el)
                 . PlacedObject (findPlacement elc)
      mkBaseObject = mkObject . BaseObject
      getBox e = Box (findFloat "Height" e) (findFloat "Width" e)
                 (findFloat "Length" e)
      getSph e = Sphere (findFloat "Angle1" e) (findFloat "Angle2" e)
                 (findFloat "Angle3" e) (findFloat "Radius" e)
      getCyl e = Cylinder (findFloat "Angle" e) (findFloat "Height" e)
                 (findFloat "Radius" e)
      getCon e = Cone (findFloat "Angle" e) (findFloat "Radius1" e)
                 (findFloat "Radius2" elc) (findFloat "Height" e)
      getTor e = Torus (findFloat "Angle1" e) (findFloat "Angle2" e)
                 (findFloat "Angle3" e) (findFloat "Radius1" e)
                 (findFloat "Radius2" e)
      getCir e = Circle (findFloat "StartAngle" e) (findFloat "EndAngle" e)
                 (findFloat "Radius" e)
      getCut e = Cut (findRef "Base" e) (findRef "Tool" e)
      getCom e = Common (findRef "Base" e) (findRef "Tool" e)
      getSec e = Section (findRef "Base" e) (findRef "Tool" e)
      getFus e = Fusion (findRef "Base" e) (findRef "Tool" e)
      getExt e = Extrusion (findRef "Base" e) 3.14159 --TODO
      elc = child el
getObject _ = error "undefined object"


mkRectangle :: Element ->IO NamedObject
mkRectangle ef = do
        let e = child ef
            el2 = childByNameAttr "Shape" e
            elx = childByName "Part" el2
        (bo, place) <- getBrep (getVal "file" elx, "rectangle")
        let obj = BaseObject bo
            po = PlacedObject place obj
        return $ NamedObject (getVal "name" ef) po
mkLine :: Element -> IO NamedObject
mkLine = error "line not implemented"

getVal:: String -> Element -> String
getVal s el = fromJust (findAttr (makeQName s) el)

getFloatVal:: Element -> String
getFloatVal el = getVal "value" el2
    where
        el2 = childByName "Float" el

getPlacementVals :: Element -> (String ,String ,String ,String ,String ,String
                               ,String)
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

--Facade function that translates the parsed XML document
--into Haskell-FreeCAD datatype

translate:: Element -> IO Document
translate baseElement = mapM getObject $ objList baseElement
