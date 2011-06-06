module FreeCAD.Brep
where
    
import System.Process
import Text.XML.Light
import Data.Maybe
import Data.Set as Set
import FreeCAD.As

getBrep::(String, String) -> (BaseObject, Placement)
getBrep (address, "rectangle") = procRectangle (getRectangle (address, "rectangle"))

procRectangle::(Vector3, Vector3, Vector3, Vector3) -> (BaseObject, Placement)
procRectangle (a, b, c, d) = (Rectangle h l, place)
    where
        d1 = distance3 a b -- \
        d2 = distance3 a c --  > values used to compute rectangle's properties
        d3 = distance3 a d -- /
        mn = min d1 (min d2 d3) -- heigth/small edge value
        mx = max d1 (min d2 d3) -- diagonal length
        md = if (d1 /= mn)&&(d1 /= mx) then d1 else --length value
                if (d2 /= mn)&&(d2 /= mx) then d2 else
                    if (d3 /= mn)&&(d3 /= mx) then d2 else 0
        h = mn 
        l = md        
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
        rot1vecn = scalarprod3 (norm3 rot1vec) rot1vec --normalized rotation vector (for q1)
        cosAlpha1 = cos((acos ((v3DotProd (Vector3 0 1 0) hpoint)/(norm3 hpoint)))/2) --(for q1)
        sinAlpha1 = sqrt (1 - cosAlpha1**2)
        quat1 = Vector4 (sinAlpha1*(x rot1vecn)) (sinAlpha1*(y rot1vecn)) (sinAlpha1*(z rot1vecn)) cosAlpha1
        tmatrix = quat2matrix quat1
        l2point = rotate tmatrix (Vector3 (norm3 lpoint) 0 0)
        -- then we rotate l2point into lpoint
        rot2vec = v3VecProd (l2point) lpoint
        rot2vecn = scalarprod3 (norm3 rot2vec) rot2vec --normalized rotation vector (for q2)
        cosAlpha2 = cos((acos ((v3DotProd l2point lpoint)/(norm3 lpoint)))/2) --(for q2)
        sinAlpha2 = sqrt (1 - cosAlpha2**2)
        quat2 = Vector4 (sinAlpha2*(x rot2vecn)) (sinAlpha2*(y rot2vecn)) (sinAlpha2*(z rot2vecn)) cosAlpha2
        quaternion = quatProd quat1 quat2
        pos = a
        place = Placement pos quaternion
        
        
        
        
        
        
        




getRectangle::(String, String) -> (Vector3, Vector3, Vector3, Vector3)
getRectangle (address, "rectangle") = readProcess "./FreeCAD/brep_conversion/bin/brep_to_xml" [address,"rectangle"]
