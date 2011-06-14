{- |
Module      :  $Header$
Description :  definition of the datatype describing
               the abstract FreeCAD terms and and a few tools describing simple
               mathematical operations on those building-blocks (3d vectors,
               rotation matrices, rotation quaternions)
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Declaration of the abstract datatypes of FreeCAD terms
-}
--
--data structures for FreeCAD documents and objects
--
module FreeCAD.As
where

import qualified Data.Set as Set

data Vector3 = Vector3 { x::Double, y::Double, z::Double } deriving (Show, Eq, Ord)
--a vector in cartesian coordinates

data Matrix33 = Matrix33 {   a11::Double ,a12::Double ,a13::Double
                            ,a21::Double ,a22::Double ,a23::Double
                            ,a31::Double ,a32::Double ,a33::Double
                         } deriving (Show, Eq, Ord) --used as a rotation matrix

data Vector4 = Vector4 { q0::Double, q1::Double, q2::Double, q3::Double}
               deriving (Show, Eq, Ord)
-- quaternion rotational representation

data Placement = Placement { position::Vector3, orientation::Vector4 }
                 deriving (Show, Eq, Ord)

{-
-- | the placement is determined by 2 vectors:
--   the first one points to the 'center' of the objet in the space
--   the second one determines the orientation of the object in the given space
data Edgelist = []
              | 1:Edgelist
              | 0:Edgelist
-}

--reference from compound objects to 'building-blocks'
--objects made through strings or containment of the other
--objects
data BaseObject = Box Double Double Double -- Height, Width, Length
            | Cylinder Double Double Double -- Angle, Height, Radius
            | Sphere Double Double Double Double --Angle1,Angle2,Angle3,Radius
            | Cone Double Double Double Double --Angle,Radius1,Radius2,Height
            | Torus Double Double Double Double Double
            --Angle1, Angle2, Angle3, Radius1, Radius2
            | Line Double -- length
            | Circle Double Double Double --StartAngle, EndAngle, Radius
            | Rectangle Double Double --Height, Length
            deriving (Show, Eq, Ord)
          --TODO: Plane, Vertex, etc..



data Object = BaseObject BaseObject
            | Cut ExtendedObject ExtendedObject
            | Common ExtendedObject ExtendedObject
            | Fusion ExtendedObject ExtendedObject
            | Section ExtendedObject ExtendedObject
                --section of an object (intersection with a plane
            | Extrusion ExtendedObject Double --TODO
--          | Fillet, (Base::String, Edges::Edgelist, Radius::Double)),
            --not enough data in the xml
--          | Chamfer, (Base::String, Edges::Edgelist, Amount::Double)),
            --not enough data in the xml
--          | Mirror, (Base::String, Position2::Vector))
            --mirroring of an object
            deriving (Show, Eq, Ord)


data ExtendedObject = Placed PlacedObject | Ref String deriving (Show, Eq, Ord)

data PlacedObject = PlacedObject {p::Placement, o::Object} deriving (Show, Eq, Ord)

data NamedObject = NamedObject { name::String
                   , object:: PlacedObject}
                 | EmptyObject --for objects that are WIP
                   deriving (Show, Eq, Ord)

-- the first parameter is the name of the object as it is stored in the
-- FreeCAD document. the second parameter determines the placement of the object
-- (a pair of vectors) the third parameter contains the type of the object and
--a list of doubles (numbers) describing the characteristics
--of the object (e.g. dimensions, angles, etc)


type Document = [NamedObject]

-- | Datatype for FreeCAD Signatures
-- Signatures are just sets of named objects
data Sign = Sign { objects :: Set.Set NamedObject } deriving (Eq, Ord, Show)


distance3:: Vector3 -> Vector3 -> Double
distance3 (Vector3 ax ay az) (Vector3 bx by bz) = sqrt (x1*x1 + x2*x2 + x3*x3)
    where
        x1 = ax - bx
        x2 = ay - by
        x3 = az - bz

subtract3:: Vector3 -> Vector3 -> Vector3
subtract3 a b = Vector3 ex ey ez
    where
        ex = (x a) - (x b)
        ey = (y a) - (y b)
        ez = (z a) - (z b)

norm3:: Vector3 -> Double
norm3 a = distance3 a (Vector3 0 0 0)

scalarprod3:: Double -> Vector3 ->Vector3
scalarprod3 a (Vector3 bx by bz) = Vector3 abx aby abz
    where
        abx = a*bx
        aby = a*by
        abz = a*bz

median3:: [Vector3] -> Vector3
median3 a = scalarprod3 (fromIntegral (length a)) (v3Sum a)

v3Sum:: [Vector3] -> Vector3
v3Sum [a,b] = Vector3 xc yc zc
    where
        xc = (x a)*(x b)
        yc = (y a)*(y b)
        zc = (z a)*(z b)
v3Sum (a:b:as) = v3Sum (c:as)
    where
        xc = (x a)*(x b)
        yc = (y a)*(y b)
        zc = (z a)*(z b)
        c = Vector3 xc yc zc

v3DotProd:: Vector3 -> Vector3 -> Double
v3DotProd v1 v2 = (x v1)*(x v2) + (y v1)*(y v2) + (z v1)*(z v2)

v4DotProd:: Vector4 -> Vector4 -> Double
v4DotProd v1 v2 = (q0 v1)*(q0 v2)+(q1 v1)*(q1 v2)+(q2 v1)*(q2 v2)+
                  (q3 v1)*(q3 v2)

v3VecProd:: Vector3 -> Vector3 -> Vector3
v3VecProd v1 v2 = Vector3 m n p
    where
        m = (y v1)*(z v2) - (z v1)*(y v2)
        n = (z v1)*(x v2) - (x v1)*(z v2)
        p = (x v1)*(y v2) - (y v1)*(x v2)

quatProd:: Vector4 -> Vector4 -> Vector4
quatProd v1 v2 = Vector4 m n p q
    where
        m = (q3 v2)*(q0 v1)+(q2 v2)*(q1 v1)-(q1 v2)*(q2 v1)+(q0 v2)*(q3 v1)
        n = -(q2 v2)*(q0 v1)+(q3 v2)*(q1 v1)+(q0 v2)*(q2 v1)+(q1 v2)*(q3 v1)
        p = (q1 v2)*(q0 v1)-(q0 v2)*(q1 v1)+(q3 v2)*(q2 v1)+(q2 v2)*(q3 v1)
        q = -(q0 v2)*(q0 v1)-(q1 v2)*(q1 v1)-(q2 v2)*(q2 v1)+(q3 v2)*(q3 v1)

-- from quaternion to rotation matrix
quat2matrix:: Vector4 -> Matrix33
quat2matrix q = Matrix33 m11 m12 m13 m21 m22 m23 m31 m32 m33
             where
                m11 = (1 - 2*p2**2 - 2*p3**2)
                m12 = (2*(p1*p2 - p3*p4))
                m13 = (2*(p1*p3 + p2*p4))
                m21 = (2*(p1*p2 + p3*p4))
                m22 = (1 - 2*p1**2 - 2*p3**2)
                m23 = (2*(p2*p3 - p1*p4))
                m31 = (2*(p1*p3 - p2*p4))
                m32 = (2*(p1*p4 + p2*p3))
                m33 = (1 - 2*p1**2 - 2*p2**2)
                p1 = q0 q
                p2 = q1 q
                p3 = q2 q
                p4 = q3 q

rotate:: Matrix33 -> Vector3 -> Vector3
rotate a v = Vector3 xx yy zz
    where
        xx = (a11 a)*(x v) + (a12 a)*(y v) + (a13 a)*(z v)
        yy = (a21 a)*(x v) + (a22 a)*(y v) + (a23 a)*(z v)
        zz = (a31 a)*(x v) + (a32 a)*(y v) + (a33 a)*(z v)
