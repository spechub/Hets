{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{- |
Module      :  ./CSL/Logic_CSL.hs
Description :  Instance of class Logic for CSL
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the CSL logic
   Also the instances for Syntax and Category.

see
Dominik Dietrich, Lutz Schröder, and Ewaryst Schulz:
Formalizing and Operationalizing Industrial Standards.
D. Giannakopoulou and F. Orejas (Eds.): FASE 2011, LNCS 6603, pp. 81–95, 2011.
-}


module CSL.Logic_CSL where

import ATC.ProofTree ()

import CSL.AS_BASIC_CSL
import CSL.ATC_CSL ()
import CSL.Analysis
import CSL.Morphism
import CSL.Parse_AS_Basic
import CSL.ReduceProve
import CSL.Sign
import CSL.Symbol
import CSL.Tools

import qualified Data.Map as Map
import Data.Monoid

import Logic.Logic

-- | Lid for reduce logic
data CSL = CSL

instance Show CSL where
    show _ = "EnCL"

instance Language CSL where
    description _ = "A Domain-Specific Language for Engineering Calculations\n"
-- language_name _ = "EnCL"

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
    symKind CSL _ = "op"

instance Semigroup BASIC_SPEC where
    (Basic_spec l1) <> (Basic_spec l2) = Basic_spec $ l1 ++ l2
instance Monoid BASIC_SPEC where
    mempty = Basic_spec []

-- | Syntax of CSL logic
instance Syntax CSL BASIC_SPEC Symbol
    SYMB_ITEMS SYMB_MAP_ITEMS where
         parse_basic_spec CSL = parseBasicSpec
         parse_symb_items CSL = parseSymbItems
         parse_symb_map_items CSL = parseSymbMapItems

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
{- matches       CSL            = Symbol.matches
stat_symb_items CSL          = mkStatSymbItems
stat_symb_map_items CSL      = mkStatSymbMapItem -}
          morphism_union CSL = morphismUnion
{- induced_from_morphism CSL    = inducedFromMorphism
induced_from_to_morphism CSL = inducedFromToMorphism -}
