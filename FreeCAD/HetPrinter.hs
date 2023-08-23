{- |
Module      :  ./FreeCAD/HetPrinter.hs
Description :  print the HasCASL representation of FreeCAD terms
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Printing of the HasCASL specification of a FreeCAD document
-}

module FreeCAD.HetPrinter where

import FreeCAD.As
import Common.DocUtils
import Common.Doc
import Common.Id

-- | Pretty printing 'Double'
instance Pretty Double where
    pretty = sidDoc . mkSimpleId . show

instance Pretty Vector3 where
    pretty v = hcat [text "V", lparen, sepByCommas $ map pretty [x v, y v, z v], rparen]

instance Pretty Vector4 where
    pretty v = hcat [text "Q", lparen, sepByCommas $ map pretty [q0 v, q1 v, q2 v, q3 v], rparen]

instance Pretty Placement where
    pretty p1 =
      hcat [text "Placement", lparen, sepByCommas [pretty $ position p1, pretty $ orientation p1], rparen]

printBO :: BaseObject -> Doc
printBO (Box h w l) = hcat [text "BBox", lparen, sepByCommas [pretty l, pretty w, pretty h], rparen]
printBO (Cylinder a h r) = hcat [text "BCylinder" , lparen, sepByCommas [pretty a, pretty h, pretty r], rparen]
printBO (Sphere a1 a2 a3 r) = hcat [text "BCylinder" , lparen, sepByCommas [pretty a1, pretty a2, pretty a3, pretty r], rparen]
printBO (Cone a r1 r2 h) = hcat [text "BCone" , lparen, sepByCommas [pretty a, pretty r1, pretty r2, pretty h], rparen]
printBO (Torus a1 a2 a3 r1 r2) = hcat [text "BTorus" , lparen, sepByCommas [pretty a1, pretty a2, pretty a3, pretty r1, pretty r2], rparen]
printBO (Line a) = hcat [text "BLine" , lparen, pretty a, rparen]
printBO (Circle sa ea r) = hcat [text "BCircle" , lparen, sepByCommas [pretty sa, pretty ea, pretty r], rparen]
printBO (Rectangle h w) = hcat [text "BRectangle" , lparen, sepByCommas [pretty h, pretty w], rparen]

instance Pretty BaseObject where
    pretty = printBO

printObject :: Object -> Doc
printObject (BaseObject bo) = pretty bo
printObject ( Cut eo1 eo2) = text "Cut" <+> hcat [lparen, sepByCommas [pretty eo1, pretty eo2], rparen]
printObject ( Common eo1 eo2) = text "Common" <+> hcat [lparen, sepByCommas [pretty eo1, pretty eo2], rparen]
printObject ( Fusion eo1 eo2) = text "Fusion" <+> hcat [lparen, sepByCommas [pretty eo1, pretty eo2], rparen]
-- printObject ( Section eo1 eo2) = text "Section" <+> brackets $ sepByCommas [pretty eo1, pretty eo2]
printObject ( Extrusion eo d) = text "Extrusion" <+> hcat [lparen, sepByCommas [pretty eo, pretty d], rparen]

instance Pretty Object where
    pretty = printObject

printEO :: ExtendedObject -> Doc
printEO (Placed po) = pretty po
printEO (Ref s) = text s

printPO :: PlacedObject -> Doc
printPO (PlacedObject plc obj) = text "PObj = " <+> hcat [text "PObj", lparen, sepByCommas [pretty obj, pretty plc], rparen, text ";"]

printDoc :: String -> Document -> Doc
printDoc name a = vcat [header, vcat [text "  ops", hcat [text "    ", vcat $ map pretty a]], end]
  where
    header = vcat [logic, imports, specname]
    logic = text "logic HasCASL"
    imports = text "from HasCASL/Real3D/FreeCAD/FreeCAD get FCObject"
    specname = hcat [text "spec ", text name, text " = FCObject ", text "then"]
    end = text "end"

instance Pretty ExtendedObject where
    pretty = printEO

instance Pretty PlacedObject where
    pretty = printPO

instance Pretty NamedObject where
    pretty no = hcat [pretty (name no), colon, pretty $ object no]
  -- $+$

-- instance GetRange NamedObject

instance Pretty Sign where
    pretty = pretty . objects
