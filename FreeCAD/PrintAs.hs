{- |
Module      :  ./FreeCAD/PrintAs.hs
Description :  print the abstract syntax of FreeCAD terms
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Printing of the abstract syntax of FreeCAD terms
-}

module FreeCAD.PrintAs where

import FreeCAD.As
import Common.DocUtils
import Common.Doc
import Common.Id

-- | Pretty printing 'Double'
instance Pretty Double where
    pretty = sidDoc . mkSimpleId . show

instance Pretty Vector3 where
    pretty v = pretty (x v, y v, z v)

instance Pretty Matrix33 where
    pretty m = vcat [lparen <+> rows, rparen] where
                         rows = vcat [row1, row2, row3]
                         row a b c = sepByCommas $ map pretty [a m, b m, c m]
                         row1 = row a11 a12 a13
                         row2 = row a21 a22 a23
                         row3 = row a31 a32 a33


instance Pretty Vector4 where
    pretty v = parens $ sepByCommas $ map pretty [q0 v, q1 v, q2 v, q3 v]

instance Pretty Placement where
    pretty p1 =
      brackets $ sepBySemis [pretty $ position p1, pretty $ orientation p1]

printBO :: BaseObject -> Doc
printBO (Box h w l) = text "Box" <+> vcat [hrow, wrow, lrow] where
        hrow = hcat [ text "Height ", pretty h]
        wrow = hcat [ text "Width  ", pretty w]
        lrow = hcat [ text "Length ", pretty l]
printBO (Cylinder a h r) = text "Cylinder" <+> vcat [arow, hrow, rrow] where
        arow = hcat [ text "Angle  ", pretty a]
        hrow = hcat [ text "Heigth ", pretty h]
        rrow = hcat [ text "Radius ", pretty r]
printBO (Sphere a1 a2 a3 r) = text "Sphere" <+>
                              vcat [a1row, a2row, a3row, rrow] where
        a1row = hcat [ text "Angle1 ", pretty a1]
        a2row = hcat [ text "Angle2 ", pretty a2]
        a3row = hcat [ text "Angle3 ", pretty a3]
        rrow = hcat [ text "Radius ", pretty r]
printBO (Cone a r1 r2 h) = text "Cone" <+> vcat [arow, brow, hrow, rrow] where
        arow = hcat [ text "Angle   ", pretty a]
        brow = hcat [ text "Radius1 ", pretty r1]
        hrow = hcat [ text "Radius2 ", pretty r2]
        rrow = hcat [ text "Heigth  ", pretty h]
printBO (Torus t1 t2 t3 t4 t5) = text "Torus" <+>
                                 vcat [t1r, t2r, t3r, t4r, t5r] where
        t1r = hcat [ text "Angle1  ", pretty t1]
        t2r = hcat [ text "Angle2  ", pretty t2]
        t3r = hcat [ text "Angle3  ", pretty t3]
        t4r = hcat [ text "Radius1 ", pretty t4]
        t5r = hcat [ text "Radius2 ", pretty t5]
printBO (Line a) = text "Line" <+> hcat [ text "Length ", pretty a]
printBO (Circle a h r) = text "Circle" <+> vcat [arow, hrow, rrow] where
        arow = hcat [ text "sAngle  ", pretty a]
        hrow = hcat [ text "eAngle  ", pretty h]
        rrow = hcat [ text "Radius ", pretty r]
printBO (Rectangle h w) = text "Rectangle" <+> vcat [hrow, wrow] where
        hrow = hcat [ text "Heigth ", pretty h]
        wrow = hcat [ text "Width  ", pretty w]

instance Pretty BaseObject where
    pretty = printBO

printObject :: Object -> Doc
printObject (BaseObject bo) = pretty bo
printObject ( Cut eo1 eo2) = text "Cut" <+> vcat [pretty eo1, pretty eo2]
printObject ( Common eo1 eo2) = text "Common" <+> vcat [pretty eo1, pretty eo2]
printObject ( Fusion eo1 eo2) = text "Fusion" <+> vcat [pretty eo1, pretty eo2]
printObject ( Section eo1 eo2) = text "Section" <+> vcat [pretty eo1, pretty eo2]
printObject ( Extrusion eo d) = text "Extrusion" <+> vcat [pretty eo, pretty d]

instance Pretty Object where
    pretty = printObject

printEO :: ExtendedObject -> Doc
printEO (Placed po) = pretty po
printEO (Ref s) = text s

printPO :: PlacedObject -> Doc
printPO (PlacedObject plc obj) = vcat [pretty obj, text "place" <+> pretty plc]

printDoc :: Document -> Doc
printDoc a = vcat $ map pretty a

instance Pretty ExtendedObject where
    pretty = printEO

instance Pretty PlacedObject where
    pretty = printPO

instance Pretty NamedObject where
    pretty no = lbrack $+$ space <+>
        hcat [doubleQuotes $ pretty $ name no, colon, space, pretty $ object no]
        $+$ rbrack

instance GetRange NamedObject

instance Pretty Sign where
    pretty = pretty . objects
