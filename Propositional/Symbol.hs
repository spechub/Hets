{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of symbols for propositional logic
-}


module Propositional.Symbol 
    ( 
     Symbol (..)           -- Symbol type
    , pretty               -- pretty printing for Symbols
    , symOf                -- Extracts the symbols out of a signature
    , getSymbolMap         -- Determines the symbol map
    , getSymbolName        -- Determines the name of a symbol
    ) where

import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Propositional.Sign as Sign
import qualified Propositional.Morphism as Morphism

-- | Datatype for symbols
data Symbol = Symbol {symName :: Id.Id}
            deriving (Show, Eq, Ord)

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = pretty $ symName x

-- | Extraction of symbols from a signature
symOf :: Sign.Sign -> Set.Set Symbol
symOf  x = foldr (\y -> Set.insert $ Symbol {symName = y}) Set.empty $ 
           Set.toList $ Sign.items x

-- | Determines the symbol map of a morhpism
getSymbolMap :: Morphism.Morphism -> Map.Map Symbol Symbol
getSymbolMap f = foldr 
                 (\(x,y) -> Map.insert Symbol{symName = x} 
                            Symbol{symName = y}) 
                 Map.empty $ Map.assocs $ Morphism.propMap f

-- | Determines the name of a symbol
getSymbolName :: Symbol -> Id.Id
getSymbolName sym = symName sym
