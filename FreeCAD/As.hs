{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./FreeCAD/As.hs
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

module FreeCAD.As where

import Data.Data
import qualified Data.HashSet as Set
import GHC.Generics (Generic)
import Data.Hashable

import Common.ATerm.ConvInstances () -- for ATC instances

data Vector3 =
  Vector3 { x :: Double, y :: Double, z :: Double }
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Vector3

data Matrix33 = Matrix33 { a11 :: Double , a12 :: Double , a13 :: Double
                            , a21 :: Double , a22 :: Double , a23 :: Double
                            , a31 :: Double , a32 :: Double , a33 :: Double
                         } deriving (Show, Eq, Ord, Typeable, Data)
  -- used as a rotation matrix

data Vector4 = Vector4 { q0 :: Double, q1 :: Double, q2 :: Double, q3 :: Double}
               deriving (Show, Eq, Ord, Typeable, Data, Generic)
-- quaternion rotational representation

instance Hashable Vector4

data Placement = Placement { position :: Vector3, orientation :: Vector4 }
                 deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Placement

{-
--   the placement is determined by 2 vectors:
--   the first one points to the 'center' of the objet in the space
--   the second one determines the orientation of the object in the given space
data Edgelist = []
              | 1:Edgelist
              | 0:Edgelist

  reference from compound objects to 'building-blocks'
  objects made through strings or containment of the other
  objects
-}
data BaseObject = Box Double Double Double -- Height, Width, Length
            | Cylinder Double Double Double -- Angle, Height, Radius
            | Sphere Double Double Double Double -- Angle1,Angle2,Angle3,Radius
            | Cone Double Double Double Double -- Angle,Radius1,Radius2,Height
            | Torus Double Double Double Double Double
            -- Angle1, Angle2, Angle3, Radius1, Radius2
            | Line Double -- length
            | Circle Double Double Double -- StartAngle, EndAngle, Radius
            | Rectangle Double Double -- Height, Length
            deriving (Show, Eq, Ord, Typeable, Data, Generic)
          -- TODO: Plane, Vertex, etc..

instance Hashable BaseObject

data Object = BaseObject BaseObject
            | Cut ExtendedObject ExtendedObject
            | Common ExtendedObject ExtendedObject
            | Fusion ExtendedObject ExtendedObject
            | Extrusion ExtendedObject Vector3
            | Section ExtendedObject ExtendedObject
            deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Object

{- --| Fillet, (Base::String, Edges::Edgelist, Radius::Double)),
            --not enough data in the xml
            --| Chamfer, (Base::String, Edges::Edgelist, Amount::Double)),
            --not enough data in the xml
            --| Mirror, (Base::String, Position2::Vector))
            --mirroring of an object
-}

data ExtendedObject = Placed PlacedObject | Ref String
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable ExtendedObject

data PlacedObject =
  PlacedObject {p :: Placement, o :: Object}
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable PlacedObject

data NamedObject = NamedObject { name :: String
                   , object :: PlacedObject}
                 | EmptyObject -- for objects that are WIP
                   deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable NamedObject

{- the first parameter is the name of the object as it is stored in the
FreeCAD document. the second parameter determines the placement of the object
(a pair of vectors) the third parameter contains the type of the object and
a list of doubles (numbers) describing the characteristics
of the object (e.g. dimensions, angles, etc) -}

type Document = [NamedObject]

{- | Datatype for FreeCAD Signatures
Signatures are just sets of named objects -}

data Sign = Sign { objects :: Set.HashSet NamedObject }
  deriving (Show, Eq, Ord, Typeable, Data)
