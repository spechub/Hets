{- |
Module      :  ./FreeCAD/XMLPrinter.hs
Description :  XML Printer function for FreeCAD datatypes
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Declaration of the abstract datatypes of FreeCAD terms
-}


module FreeCAD.XMLPrinter where

import Text.XML.Light
import FreeCAD.As
import qualified Data.HashSet as Set

exportXMLFC :: Sign -> String
exportXMLFC = ppTopElement . doc2XML . Set.toList . objects

makeAttr :: String -> String -> Attr
makeAttr key = Attr (unqual key)

doc2XML :: Document -> Element
doc2XML list = unode "document" (map sendNamedObj list)

sendNamedObj :: NamedObject -> Element
sendNamedObj no = add_attr att (unode "Object" (getNOChildren no)) where
    att = Attr (unqual "name") (name no)

getNOChildren :: NamedObject -> [Element]
getNOChildren no = [makePlaceElem place, makeObjElem obj] where
    pobj = object no
    obj = o pobj
    place = p pobj

makePlaceElem :: Placement -> Element
makePlaceElem pl = unode "placement" attrList
    where
      attrList = [xAt, yAt, zAt, q0At, q1At, q2At, q3At]
      mkp a b = Attr (unqual a) (show b)
      mko a b = Attr (unqual a) (show b)
      xAt = mkp "x" (x $ position pl)
      yAt = mkp "y" (y $ position pl)
      zAt = mkp "z" (z $ position pl)
      q0At = mko "q0" (q0 $ orientation pl)
      q1At = mko "q1" (q1 $ orientation pl)
      q2At = mko "q2" (q2 $ orientation pl)
      q3At = mko "q3" (q3 $ orientation pl)

mkNumAtt :: Show a => String -> a -> Attr
mkNumAtt key num = Attr (unqual key) (show num)

makeObjElem :: Object -> Element
makeObjElem obj = case obj of
                    BaseObject bo -> makeBOElem bo
                    Cut eo1 eo2 -> mk2refs "cut" eo1 eo2
                    Common eo1 eo2 -> mk2refs "common" eo1 eo2
                    Fusion eo1 eo2 -> mk2refs "fusion" eo1 eo2
                    Section eo1 eo2 -> mk2refs "section" eo1 eo2
                    Extrusion eo1 v3 -> mk1refs "extrusion" eo1 v3
    where
      mkRefAtt key eo = Attr (unqual key) (getEORef eo)
      mk2refs consType ref1 ref2 =
          unode consType [mkRefAtt "base" ref1, mkRefAtt "tool" ref2]
      mk1refs consType ref v3 =
          unode consType [mkRefAtt "base" ref, mkNumAtt "xval" (x v3),
                          mkNumAtt "yval" (y v3), mkNumAtt "zval" (z v3)]

getEORef :: ExtendedObject -> String
getEORef eo = case eo of
           Ref s -> s
           Placed _ -> error "cannot get reference"

makeBOElem :: BaseObject -> Element
makeBOElem obj = case obj of
                   Box a1 a2 a3 ->
                       unode "box" [mkNumAtt "height" a1, mkNumAtt "width" a2,
                        mkNumAtt "length" a3]
                   Cylinder a1 a2 a3 ->
                       unode "cylinder" [mkNumAtt "angle" a1,
                        mkNumAtt "height" a2, mkNumAtt "radius" a3]
                   Sphere a1 a2 a3 a4 ->
                       unode "sphere" [mkNumAtt "angle1" a1,
                        mkNumAtt "angle2" a2, mkNumAtt "angle3" a3,
                        mkNumAtt "radius" a4]
                   Cone a1 a2 a3 a4 ->
                       unode "cone" [mkNumAtt "angle" a1, mkNumAtt "radius1" a2,
                        mkNumAtt "radius2" a3, mkNumAtt "height" a4]
                   Torus a1 a2 a3 a4 a5 ->
                       unode "torus" [mkNumAtt "angle1" a1,
                        mkNumAtt "angle2" a2, mkNumAtt "angle3" a3,
                        mkNumAtt "radius1" a4, mkNumAtt "radius2" a5]
                   Line a1 -> unode "line" (mkNumAtt "length" a1)
                   Circle a1 a2 a3 ->
                       unode "circle" [mkNumAtt "startang" a1,
                        mkNumAtt "endang" a2, mkNumAtt "radius" a3]
                   Rectangle a1 a2 ->
                       unode "rectangle" [mkNumAtt "height" a1,
                        mkNumAtt "length" a2]
