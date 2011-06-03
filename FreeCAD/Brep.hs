module FreeCAD.Brep
where
    
import System.Process
import Text.XML.Light
import Data.Maybe
import Data.Set as Set
import FreeCAD.As

getBrep::(String, String) -> (Element, Placement)
getBrep (address, "rectangle") = procRectangle (getRectangle (address, "rectangle"))

procRectangle::(Vector3, Vector3, Vector3, Vector3) -> (Element, Placement)
procRectangle [a, b, c, d] = (Rectangle h l, )
    where
        d1 = distance a b
        d2 = distance a c 
        d3 = distance a d
        mx = max d1 (max d2 d3)
        mn = min d1 (min d2 d3)
        md = sqrt( mx*mx - mn*mn)
        h = mn
        l = md
        

getRectangle::String-> String -> [Vector3, Vector3, Vector3, Vector3]
getRectangle (address, "rectangle") = readProcess "./FreeCAD/brep_conversion/bin/brep_to_xml" [address,"rectangle"]
