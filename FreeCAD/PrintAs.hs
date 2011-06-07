{- |
Module      :  $Header$
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
    pretty v =  pretty (x v, y v, z v)

instance Pretty Matrix33 where
    pretty m =  vcat [lparen <> rows, rparen] where
                         rows = vcat [row1, row2, row3]
                         row a b c = sepByCommas $ map pretty [a m, b m, c m]
                         row1 = row a11 a12 a13
                         row2 = row a21 a22 a23
                         row3 = row a31 a32 a33
