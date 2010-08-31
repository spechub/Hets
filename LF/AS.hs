{- |
Module      :  $Header$
Description :  Abstract syntax for the Edinburgh Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable

-}

module LF.AS
       ( BASIC_SPEC (..)
       , BASIC_ITEM (..)
       , SYMB_ITEMS (..)
       , SYMB_MAP_ITEMS (..)
       , SYMB_OR_MAP (..)
       ) where

import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils

-- grammar for basic specs
data BASIC_SPEC = Basic_spec [Annoted BASIC_ITEM]
                  deriving Show

instance GetRange BASIC_SPEC

data BASIC_ITEM = Decl String
                | Form String
                  deriving Show

-- grammar for symbols and symbol maps
data SYMB_ITEMS = Symb_items [String]
                  deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP]
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb String
                 | Symb_map String String
                   deriving (Show, Eq)

-- pretty printing
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEM where
    pretty = printBasicItem
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Decl d) = pretty d <> dot
printBasicItem (Form f) = dot <+> pretty f

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs) = ppWithCommas xs

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs) = ppWithCommas xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb s) = pretty s
printSymbOrMap (Symb_map s t) = pretty s <+> mapsto <+> pretty t
