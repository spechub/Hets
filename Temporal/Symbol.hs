{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./Temporal/Symbol.hs
Description :  Symbols of propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for propositional logic
-}


module Temporal.Symbol
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

import Data.Data
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map

import qualified Temporal.Sign as Sign
import qualified Temporal.Morphism as Morphism

import GHC.Generics (Generic)
import Data.Hashable

-- | Datatype for symbols
newtype Symbol = Symbol {symName :: Id.Id}
            deriving (Show, Eq, Ord, Typeable, Generic)

instance Hashable Symbol

instance Pretty Symbol where
    pretty = printSymbol

instance Id.GetRange Symbol where
    getRange = Id.getRange . symName

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

-- | Extraction of symbols from a signature
symOf :: Sign.Sign -> Set.HashSet Symbol
symOf x = Set.foldr (\ y -> Set.insert Symbol {symName = y}) Set.empty $
           Sign.items x

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.HashMap Symbol Symbol
getSymbolMap f = Map.foldrWithKey
                 (\ k a -> Map.insert Symbol {symName = k} Symbol {symName = a})
                 Map.empty $ Morphism.propMap f

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
matches s1 s2 = s1 == s2

-- | application function for Symbol Maps
applySymMap :: Map.HashMap Symbol Symbol -> Symbol -> Symbol
applySymMap smap idt = Map.findWithDefault idt idt smap
