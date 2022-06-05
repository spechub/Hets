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
printPredItem = undefined

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec = undefined

printBasicItem :: BASIC_ITEM -> Doc
printBasicItem = undefined

printSymbol :: SYMB -> Doc
printSymbol = undefined 

printSymbItems :: SYMB_ITEMS -> Doc
 printSymbItems = undefined

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap = undefined

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems = undefined

