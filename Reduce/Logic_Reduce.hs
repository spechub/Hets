{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for Reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the propositional logic
   Also the instances for Syntax and Category.
-}


module Reduce.Reduce where

import Logic.Logic

import Reduce.Sign
import Reduce.Morphism
import Reduce.AS_BASIC_Reduce
import Reduce.Parse_AS_Basic
import Reduce.Analysis
import Reduce.Tools
import qualified Data.Map as Map
import Common.ProofTree

-- | Lid for reduce logic
data Reduce = Reduce deriving Show

instance Language Reduce where
    description _ = "Reduce Logic\n"

-- | Instance of Category for Reduce logic
instance Category Sign Morphism where
    -- Identity morhpism
    ide = idMor
    -- Returns the domain of a morphism
    dom = source
    -- Returns the codomain of a morphism
    cod = target
    -- check if morphism is inclusion
    isInclusion = Map.null . propMap
    -- tests if the morphism is ok
    legal_mor = isLegalMorphism
    -- composition of morphisms
    composeMorphisms = composeMor

-- | Instance of Sentences for reduce logic
instance Sentences Reduce Cmd
    Sign Morphism Symbol where
    negation Reduce = Just . negateFormula
    -- returns the set of symbols
    sym_of Reduce = symOf
    -- returns the symbol map
    symmap_of Reduce = getSymbolMap
    -- returns the name of a symbol
    sym_name Reduce = getSymbolName
    -- translation of sentences along signature morphism
    map_sen Reduce = mapSentence
    -- there is nothing to leave out
    simplify_sen Reduce _ = id

-- | Syntax of Reduce logic
instance Syntax Reduce BASIC_SPEC
    SYMB_ITEMS SYMB_MAP_ITEMS where
         parse_basic_spec Reduce = Just basicSpec
         parse_symb_items Reduce = Just symbItems
         parse_symb_map_items Reduce = Just symbMapItems

-- | Instance of Logic for reduce logc
instance Logic Reduce
    PropSL                    -- Sublogics
    BASIC_SPEC                -- basic_spec
    Cmd                    -- sentences are CAS commands
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
    ProofTree                      -- proof_tree
    where
      stability Reduce     = Experimental
      top_sublogic Reduce  = Sublogic.top
      all_sublogics Reduce = sublogics_all
      empty_proof_tree Reduce = emptyProofTree
      -- supplied provers
      provers Reduce = []



-- | Static Analysis for reduce logic
instance StaticAnalysis Reduce
    BASIC_SPEC                -- basic_spec
    Cmd                   -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
        where
          basic_analysis Reduce           =
              Just basicReduceAnalysis
          empty_signature Reduce          = emptySig
          is_subsig Reduce                = isSubSigOf
          subsig_inclusion Reduce s = return . inclusionMap s
          signature_union Reduce          = sigUnion
          symbol_to_raw Reduce            = symbolToRaw
          id_to_raw     Reduce            = idToRaw
          matches       Reduce            = Symbol.matches
          stat_symb_items Reduce          = mkStatSymbItems
          stat_symb_map_items Reduce      = mkStatSymbMapItem
          morphism_union Reduce           = morphismUnion
          induced_from_morphism Reduce    = inducedFromMorphism
          induced_from_to_morphism Reduce = inducedFromToMorphism
          signature_colimit Reduce  = signatureColimit




-- =============================================================================

basic_analysis = basicPropositionalAnalysis
empty_signature = emptySig
is_subsig = isSubSigOf
subsig_inclusion  s = return . inclusionMap s
signature_union  sigUnion
symbol_to_raw = symbolToRaw
id_to_raw = idToRaw
matches = Symbol.matches
stat_symb_items  = mkStatSymbItems
stat_symb_map_items = mkStatSymbMapItem
morphism_union = morphismUnion
induced_from_morphism = inducedFromMorphism
induced_from_to_morphism = inducedFromToMorphism
signature_colimit = signatureColimit
