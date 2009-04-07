{- |
Module      :  $Header$
Description :  Symbol definition for first-order logic with dependent types (DFOL)
-}

module DFOL.Symbol where

import DFOL.AS_DFOL
import Common.Doc
import Common.DocUtils

--a symbol is just a name
data Symbol = Symbol {name :: NAME} deriving (Show, Eq, Ord)

-- pretty printing
instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol (Symbol s) = pretty s
