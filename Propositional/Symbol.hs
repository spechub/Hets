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
    ) where

import Common.Id
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set
import Propositional.Sign 

-- | Datatype for symbols
data Symbol = Symbol {symName :: Common.Id.Id}
            deriving (Show, Eq, Ord)

instance Pretty Symbol where
    pretty = printSymbol

printSymbol :: Symbol -> Doc
printSymbol x = idDoc $ symName x

-- | Extraction of symbols from a signature
symOf :: Sign -> Set.Set Symbol
symOf  x = foldr (\y -> Set.insert $ Symbol {symName = y}) Set.empty $ 
           Set.toList $ items x
