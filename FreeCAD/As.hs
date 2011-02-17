--
--data structures for FreeCAD documents and objects
--
module FreeCAD.As 
    where

data Vector = Vector { x::Double, y::Double, z::Double } deriving Show 
--a vector in cartesian coordinates

data Placement = Placement { position::Vector, orientation::Vector } deriving Show 

{-
-- | the placement is determined by 2 vectors:
--   the first one points to the 'center' of the objet in the space
--   the second one determines the orientation of the object in the given space
data Edgelist = []
              | 1:Edgelist
              | 0:Edgelist
-}

--reference from compound objects to 'building-blocks' objects made through strings or containment of the other 
--objects
data BaseObject = Box Double Double Double -- Height, Width, Length
            | Cylinder Double Double Double -- Angle, Height, Radius
            | Sphere Double Double Double Double --Angle1, Angle2, Angle3, Radius
            | Cone Double Double Double Double --Angle, Radius1, Radius2, Height
            | Torus Double Double Double Double Double --Angle1, Angle2, Angle3, Radius1, Radius2
--          | Line   :not enough data in the xml to determine the full properties
--          | Wire   :not enough data in the xml to determine the full properties
            | Circle Double Double Double --StartAngle, EndAngle, Radius
            | Rectangle Double Double --Height, Length
            deriving Show 
          --TODO: Plane, Vertex, etc..



data Object = BaseObject BaseObject 
            | Cut ExtendedObject ExtendedObject --difference between object1 and object2
            | Common ExtendedObject ExtendedObject --intersection of two objects
            | Fusion ExtendedObject ExtendedObject  --union of two objects
            | Section ExtendedObject ExtendedObject  --section of an object (intersection with a plane
--          | Fillet, (Base::String, Edges::Edgelist, Radius::Double)), --not enough data in the xml
--          | Chamfer, (Base::String, Edges::Edgelist, Amount::Double)), --not enough data in the xml
--          | Mirror, (Base::String, Position2::Vector)) --mirroring of an object 
            deriving Show 

 
data ExtendedObject = Placed PlacedObject | Ref String deriving Show 

data PlacedObject = PlacedObject Placement Object deriving Show 

data NamedObject = NamedObject { name::String
                   , object:: PlacedObject}  
                 deriving Show


-- the first parameter is the name of the object as it is stored in the FreeCAD document
-- the second parameter determines the placement of the object (a pair of vectors)
-- the third parameter contains the type of the object and
--a list of doubles (numbers) describing the characteristics
--of the object (e.g. dimensions, angles, etc)


type Document = [NamedObject]
