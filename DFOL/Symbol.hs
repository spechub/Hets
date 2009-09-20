{- |
Module      :  $Header$
Description :  Symbol definition for first-order logic
               with dependent types (DFOL)
-}

module DFOL.Symbol where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map

--a symbol is just a name
data Symbol = Symbol {name :: NAME} deriving (Show, Eq, Ord)

-- pretty printing
instance Pretty Symbol where
    pretty = printSymbol

instance GetRange Symbol where
  getRange = getRange . name

printSymbol :: Symbol -> Doc
printSymbol (Symbol s) = pretty s

-- extraction of symbols from a signature
symOf :: Sign -> Set.Set Symbol
symOf sig = Set.map Symbol $ getSymbols sig

-- constructs a symbol map from a morphism
symmapOf :: Morphism -> Map.Map Symbol Symbol
symmapOf m = Map.fromList $ map (\ (k,a) -> (Symbol k, Symbol a)) 
               $ Map.toList $ symMap m

-- returns the id of a symbol
symName :: Symbol -> Id
symName sym = mkId [name sym]

idToRaw :: Id -> Symbol
idToRaw (Id toks _ _) = Symbol $ Token (concat $ map tokStr toks) nullRange
