module NeSyPatterns.Print where

import Common.Doc
import Common.DocUtils

import NeSyPatterns.AS

{- All about pretty printing
we chose the easy way here :) -}
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty BASIC_ITEM where
    pretty = printBasicItem
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
instance Pretty Node where
    pretty = printNode

printNode :: Node -> Doc
printNode (Node mot mid _) =
  let
    ot = maybe empty pretty mot
    id' = maybe empty (brackets . pretty) mid
  in ot <> id'

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec l) = vsep $ map (printAnnoted pretty) l

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem (Path nodes) =
  fsep . punctuate (text "->") $ map pretty nodes

printSymbol :: SYMB -> Doc
printSymbol (Symb_id id') = pretty id'

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items symbs _) =
  fsep . punctuate (text ",") $ map pretty symbs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb s) = pretty s
printSymbOrMap (Symb_map s1 s2 _) = 
  pretty s1 <> text " |-> " <> pretty s2

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items l _) =
  fsep . punctuate (text ",") $ map pretty l

