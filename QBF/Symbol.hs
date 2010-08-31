{- |
Module      :  $Header$
Description :  Symbols of propositional logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  portable

Definition of symbols for propositional logic
-}


module QBF.Symbol
    (
     Symbol (..)           -- Symbol type
    , pretty               -- pretty printing for Symbols
    , symOf                -- Extracts the symbols out of a signature
    , getSymbolMap         -- Determines the symbol map
    , getSymbolName        -- Determines the name of a symbol
    , idToRaw              -- Creates a raw symbol
    , symbolToRaw          -- Convert symbol to raw symbol
    , matches              -- does a symbol match a raw symbol?
    , applySymMap          -- application function for symbol maps
    ) where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Propositional.Sign as Sign
import QBF.Morphism as Morphism

-- | Datatype for symbols
newtype Symbol = Symbol {symName :: Id.Id}
            deriving (Show, Eq, Ord)

instance Id.GetRange Symbol where
    getRange = Id.getRange . symName

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol = pretty . symName

-- | Extraction of symbols from a signature
symOf :: Sign.Sign -> Set.Set Symbol
symOf = Set.fold (\ y -> Set.insert Symbol {symName = y}) Set.empty .
           Sign.items

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.Map Symbol Symbol
getSymbolMap f =
  foldr (\ x -> Map.insert (Symbol x) (Symbol $ applyMap (propMap f) x))
  Map.empty $ Set.toList $ Sign.items $ source f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName = symName

-- | make a raw_symbol
idToRaw :: Id.Id -> Symbol
idToRaw mid = Symbol {symName = mid}

-- | convert to raw symbol
symbolToRaw :: Symbol -> Symbol
symbolToRaw = id

-- | does a smybol match a raw symbol?
matches :: Symbol -> Symbol -> Bool
matches = (==)

-- | application function for Symbol Maps
applySymMap :: Map.Map Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt smap
