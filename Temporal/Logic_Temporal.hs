{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  ./Temporal/Logic_Temporal.hs
Description :  Instance of class Logic for temporal logic
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for temporal logic
   Also the instances for Syntax and Category.
-}

module Temporal.Logic_Temporal where

import Data.Monoid ()

import Logic.Logic

import Temporal.Sign as Sign
import Temporal.Morphism as Morphism
import qualified Temporal.Symbol as Symbol

import Temporal.AS_BASIC_Temporal as AS_BASIC
import Temporal.ATC_Temporal ()

-- | Lid for termporal logic
data Temporal = Temporal deriving Show


-- | Instance of Language for temporal logic
instance Language Temporal
    where
        description Temporal = "Temporal logic"


-- | Instance of Category for temporal logic
instance Category
    Sign.Sign
    Morphism.Morphism
    where
        ide = Morphism.idMor  -- Identity morphism
        dom = Morphism.source -- Returns the domain of a morphism
        cod = Morphism.target -- Returns the codomain of a morphism
        legal_mor = Morphism.isLegalMorphism -- Tests if the morphism is ok
        composeMorphisms = Morphism.composeMor
        -- Composition of morphisms

-- | Instance of Sentences for temporal logic
instance Sentences Temporal
    AS_BASIC.FORMULA
    Sign.Sign
    Morphism.Morphism
    Symbol.Symbol
    where
        sym_of Temporal = singletonList . Symbol.symOf
        -- Returns a list of sets of symbols
        symmap_of Temporal = Symbol.getSymbolMap
        -- Returns the symbol map
        sym_name Temporal = Symbol.getSymbolName
        -- Returns the name of a symbol
        map_sen Temporal = Morphism.mapSentence
        -- Translation of sentences along signature morphism
        simplify_sen Temporal _ form = form
        -- There is nothing to leave out
        symKind Temporal _ = "prop"

instance Semigroup AS_BASIC.BASIC_SPEC where
    _ <> _ = Basic_spec
instance Monoid AS_BASIC.BASIC_SPEC where
    mempty = Basic_spec

-- | Syntax of Temporal logic
instance Syntax Temporal
    AS_BASIC.BASIC_SPEC
    Symbol.Symbol
    ()
    ()

-- | Instance of Logic for propositional logc
instance Logic Temporal
    ()                                  -- Sublogics
    AS_BASIC.BASIC_SPEC                 -- basic_spec
    AS_BASIC.FORMULA                    -- sentence
    ()                                  -- symb_items
    ()                                  -- symb_map_items
    Sign.Sign                           -- sign
    Morphism.Morphism                   -- morphism
    Symbol.Symbol                       -- symbol
    Symbol.Symbol                       -- raw_symbol
    ()                                  -- proof_tree

-- | Static Analysis for propositional logic
instance StaticAnalysis Temporal
    AS_BASIC.BASIC_SPEC                -- basic_spec
    AS_BASIC.FORMULA                   -- sentence
    ()                                 -- symb_items
    ()                                 -- symb_map_items
    Sign.Sign                          -- sign
    Morphism.Morphism                  -- morphism
    Symbol.Symbol                      -- symbol
    Symbol.Symbol                      -- raw_symbol
        where
          empty_signature Temporal = Sign.emptySig
          is_subsig Temporal = Sign.isSubSigOf
          subsig_inclusion Temporal s = return . Morphism.inclusionMap s
          signature_union Temporal = Sign.sigUnion
          symbol_to_raw Temporal = Symbol.symbolToRaw
          id_to_raw Temporal = Symbol.idToRaw
          matches Temporal = Symbol.matches
