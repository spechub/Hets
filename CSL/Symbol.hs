{- |
Module      :  $Header$
Description :  symbols for CSL
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}

module CSL.Symbol where

import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import CSL.Sign
import CSL.Morphism

-- | Datatype for symbols
newtype Symbol = Symbol {symName :: Id}
            deriving (Show, Eq, Ord)

instance GetRange Symbol where
    getRange = getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

-- | Extraction of symbols from a signature
symOf :: Sign -> Set.Set Symbol
symOf = Set.map Symbol . opIds

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism -> Map.Map Symbol Symbol
getSymbolMap f =
  Set.fold (\ x -> Map.insert (Symbol x) (Symbol $ applyMap (operatorMap f) x))
  Map.empty $ opIds $ source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id
getSymbolName = symName

-- | make a raw_symbol
idToRaw :: Id -> Symbol
idToRaw mid = Symbol {symName = mid}

-- | convert to raw symbol
symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

-- | does a smybol match a raw symbol?
matches :: Symbol -> Symbol -> Bool
matches s1 s2 = s1 == s2

-- | application function for Symbol Maps
applySymMap :: Map.Map Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt smap
