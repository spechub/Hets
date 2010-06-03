{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for CSL
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the CSL logic
   Also the instances for Syntax and Category.
-}


module CSL.Logic_CSL where

import Logic.Logic

import CSL.Sign
import CSL.Morphism
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic
import CSL.Analysis
import CSL.Tools
import CSL.Symbol
import CSL.ATC_CSL ()
import CSL.ReduceProve
import qualified Data.Map as Map
import ATC.ProofTree ()

-- | Lid for reduce logic
data CSL = CSL deriving Show

instance Language CSL where
    description _ = "CSL Logic\n"
--    language_name _ = "CSL"

-- | Instance of Category for CSL logic
instance Category Sign Morphism where
    -- Identity morhpism
    ide = idMor
    -- Returns the domain of a morphism
    dom = source
    -- Returns the codomain of a morphism
    cod = target
    -- check if morphism is inclusion
    isInclusion = Map.null . operatorMap
    -- tests if the morphism is ok
    legal_mor = isLegalMorphism
    -- composition of morphisms
    composeMorphisms = composeMor

-- | Instance of Sentences for reduce logic
instance Sentences CSL CMD
    Sign Morphism Symbol where
    negation CSL = Just . negateFormula
    -- returns the set of symbols --> including operators
    sym_of CSL = singletonList . symOf
    {- returns the symbol map -->
    the internal map only contains changes but the external symbol map
    must also contain identity mappings for all remaining symbols -}
    symmap_of CSL = getSymbolMap
    -- returns the name of a symbol --> id
    sym_name CSL = getSymbolName
    {- translation of sentences along signature morphism -->
    rename the used operators according to the morphism -}
    map_sen CSL = mapSentence
    -- there is nothing to leave out
    simplify_sen CSL _ = id

-- | Syntax of CSL logic
instance Syntax CSL BASIC_SPEC
    SYMB_ITEMS SYMB_MAP_ITEMS where
         parse_basic_spec CSL = Just basicSpec
         parse_symb_items CSL = Just symbItems
         parse_symb_map_items CSL = Just symbMapItems

-- | Instance of Logic for reduce logc
instance Logic CSL
    ()                        -- Sublogics
    BASIC_SPEC                -- basic_spec
    CMD                       -- sentences are CAS commands
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                      -- sign
    Morphism                  -- morphism
    Symbol                    -- symbol
    Symbol                    -- raw_symbol
    [EXPRESSION]              -- proof_tree
    where
      stability CSL = Experimental
      empty_proof_tree CSL = []
      -- supplied provers
      provers CSL = [reduceProver]

-- | Static Analysis for reduce logic
instance StaticAnalysis CSL
    BASIC_SPEC                -- basic_spec
    CMD                       -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                      -- sign
    Morphism                  -- morphism
    Symbol                    -- symbol
    Symbol                    -- raw_symbol
        where
          basic_analysis CSL = Just basicCSLAnalysis
          empty_signature CSL = emptySig
          is_subsig CSL = isSubSigOf
          subsig_inclusion CSL s = return . inclusionMap s
          signature_union CSL = sigUnion
          symbol_to_raw CSL = symbolToRaw
          id_to_raw CSL = idToRaw
-- matches       CSL            = Symbol.matches
-- stat_symb_items CSL          = mkStatSymbItems
-- stat_symb_map_items CSL      = mkStatSymbMapItem
          morphism_union CSL = morphismUnion
-- induced_from_morphism CSL    = inducedFromMorphism
-- induced_from_to_morphism CSL = inducedFromToMorphism
