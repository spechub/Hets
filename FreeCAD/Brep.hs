{- |
Module      :  $FreeCAD$
Description :  Hets(Haskell) end-point of the interface with the OpenCascade
               libraries. It reads the ouput of the C++ program "Brep_Reader"
               and interprets it in order to generate the data for the basic
               FreeCAD terms, which are not properly described in the file
               "Document.xml"
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Haskell layer of the Brep-reader
-}
module FreeCAD.Brep where

import System.Process
import Text.XML.Light
import Data.Maybe
import Data.Set as Set
import FreeCAD.As

getBrep::(String, String) -> IO (BaseObject, Placement)
getBrep (address, "rectangle") =
    fmap procRectangle $ getRectangle address

procRectangle::(Vector3, Vector3, Vector3, Vector3) -> (BaseObject, Placement)
procRectangle (a, b, c, d) = (Rectangle h l, place)
    where
        d1 = distance3 a b -- \
        d2 = distance3 a c --  > values used to compute rectangle's properties
        d3 = distance3 a d -- /
        mn = min d1 (min d2 d3) -- heigth/small edge value
        mx = max d1 (max d2 d3) -- diagonal length
        md = if (d1 /= mn)&&(d1 /= mx) then d1 else --length value
                if (d2 /= mn)&&(d2 /= mx) then d2 else
                    if (d3 /= mn)&&(d3 /= mx) then d3 else 0
        h = d1
        l = d3
        hh = if mn == d1 then b else --w/o rotation is on the Oy axis
                    if mn == d2 then c else
                        if mn == d3 then d else (Vector3 0 0 0)
        hpoint = subtract3 hh a
        ll = if md == d1 then b else --w/o rotation is on the Ox axis
                    if md == d2 then c else
                        if md == d3 then d else (Vector3 0 0 0)
        lpoint = subtract3 ll a
        --obtain actual rotation by 2 intermediary rotations, matching points in
        --space ( a = 0.0.0; first: hpoint = hpoint'; then: lpoint = lpoint' )
        -- 0.0.0 --> X.Y.Z
        -- first we rotate with regard to hpoint (and Oy axis)
        rot1vec = v3VecProd (Vector3 0 1 0) hpoint -- rotation vector (for q1)
        rot1vecn = scalarprod3 (norm3 rot1vec) rot1vec
        cosAa1 = cos((acos((v3DotProd(Vector3 0 1 0)hpoint)/(norm3 hpoint)))/2)
        sinAa1 = sqrt (1 - cosAa1**2)
        quat1 = Vector4 (sinAa1*(x rot1vecn)) (sinAa1*(y rot1vecn))
                        (sinAa1*(z rot1vecn)) cosAa1
        tmatrix = quat2matrix quat1
        l2point = rotate tmatrix (Vector3 (norm3 lpoint) 0 0)
        -- then we rotate l2point into lpoint
        rot2vec = v3VecProd (l2point) lpoint
        rot2vecn = scalarprod3 (norm3 rot2vec) rot2vec
        cosAa2 = cos((acos ((v3DotProd l2point lpoint)/(norm3 lpoint)))/2)
        sinAa2 = sqrt (1 - cosAa2**2)
        quat2 = Vector4 (sinAa2*(x rot2vecn)) (sinAa2*(y rot2vecn))
                        (sinAa2*(z rot2vecn)) cosAa2
        quaternion = quatProd quat1 quat2
        pos = a
        place = Placement pos quaternion
getRectangle:: String -> IO (Vector3, Vector3, Vector3, Vector3)
getRectangle address = fmap parseBrepXML $ readProcess
                        "./FreeCAD/brep_conversion/bin/brep_to_xml"
                        [concat ["/tmp/",address], "rectangle"] ""
                        --TODO fix this ^ (make it portable)

parseBrepXML:: String -> (Vector3, Vector3, Vector3, Vector3)
parseBrepXML a = getData $fromJust $parseXMLDoc a

quadFromList :: [a] -> (a,a,a,a)
quadFromList (d:b:c:[]) = error "List too short"
quadFromList (b:c:d:e) = (b,c,d, head e)

getData:: Element -> (Vector3, Vector3, Vector3, Vector3)
getData e = if (qName $elName e) == "rectangle" then
                quadFromList (Prelude.map parseVertex (elChildren e))
            else error "unsupported object type in the .brp file"

parseVertex:: Element -> Vector3
parseVertex e = Vector3 (getD "x") (getD "y") (getD "z") where
    getD x = if ( findAttr (makeQName x) e) == Nothing then
                 error "erroneous input given by c++ module"
             else read $fromJust (findAttr (makeQName x) e)
    --getD x = 0

makeQName:: String -> QName
makeQName s = QName s Nothing Nothing
