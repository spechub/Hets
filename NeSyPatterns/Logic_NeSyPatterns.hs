{-# LANGUAGE CPP, MultiParamTypeClasses #-}

{- |
Module      :  ./NeSyPatterns/Logic_NeSyPatterns.hs
Description :  Instance of class Logic for neural-symbolic patterns
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till.mossakowski@ovgu.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for neural-symbolic patterns
-}

module NeSyPatterns.Logic_NeSyPatterns where

import Logic.Logic

import OWL2.Logic_OWL2

import NeSyPatterns.Sign
import NeSyPatterns.Morphism
import NeSyPatterns.AS
import NeSyPatterns.Symbol as Symbol
import NeSyPatterns.Parse
import NeSyPatterns.Analysis

import Common.ProofTree
import ATC.ProofTree ()

import NeSyPatterns.ATC_NeSyPatterns ()

import qualified Data.Map as Map

-- | Lid for propositional logic
data NeSyPatterns = NeSyPatterns deriving Show

instance Language NeSyPatterns where
    description _ = "NeSyPatterns Logic\n"
        ++ "for more information please refer to\n"
        ++ "http://en.wikipedia.org/wiki/NeSyPatterns_logic"

-- | Instance of Category for propositional logic
instance Category Sign Morphism where
    -- Identity morhpism
    ide = idMor
    -- Returns the domain of a morphism
    dom = source
    -- Returns the codomain of a morphism
    cod = target
    -- check if morphism is inclusion
    isInclusion = Map.null . nodeMap
    -- tests if the morphism is ok
    legal_mor = isLegalMorphism
    -- composition of morphisms
    composeMorphisms = composeMor

-- | Instance of Sentences for propositional logic
instance Sentences NeSyPatterns ()
    Sign Morphism Symbol where
    negation NeSyPatterns _ = Just ()
    -- returns the set of symbols
    sym_of NeSyPatterns = singletonList . symOf
    -- returns the symbol map
    symmap_of NeSyPatterns = getSymbolMap
    -- returns the name of a symbol
    sym_name NeSyPatterns = getSymbolName
    symKind NeSyPatterns _ = "prop"
    -- translation of sentences along signature morphism
    map_sen NeSyPatterns _ = return $ return ()
    -- there is nothing to leave out
    simplify_sen NeSyPatterns _ _ = ()


instance Semigroup BASIC_SPEC where
    (Basic_spec paths1) <> (Basic_spec paths2) = Basic_spec (paths1 ++ paths2)

instance Monoid BASIC_SPEC where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2

-- - | Syntax of NeSyPatterns logic
instance Syntax NeSyPatterns BASIC_SPEC
    Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
         parsersAndPrinters NeSyPatterns =
           addSyntax "Hets" (basicSpec, pretty)
           $ makeDefault (basicSpec, pretty)
         parse_symb_items NeSyPatterns = Just symbItems
         parse_symb_map_items NeSyPatterns = Just symbMapItems

-- | Instance of Logic for propositional logc
instance Logic NeSyPatterns
    ()                    -- Sublogics
    BASIC_SPEC                -- basic_spec
    ()                   -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
    ProofTree                      -- proof_tree
    where
        -- hybridization
      parse_basic_sen NeSyPatterns = Just . const . return $ ()
      stability NeSyPatterns = Stable
      top_sublogic NeSyPatterns = ()
      all_sublogics NeSyPatterns = []
      empty_proof_tree NeSyPatterns = emptyProofTree
    -- supplied provers
      provers NeSyPatterns = []
      cons_checkers NeSyPatterns = []
      conservativityCheck NeSyPatterns = []
      data_logic NeSyPatterns = Just (Logic OWL2)

-- | Static Analysis for propositional logic
instance StaticAnalysis NeSyPatterns
    BASIC_SPEC                -- basic_spec
    ()                   -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
        where
          basic_analysis NeSyPatterns =
              Just basicNeSyPatternsAnalysis
          empty_signature NeSyPatterns = emptySig
          is_subsig NeSyPatterns = isSubSigOf
          subsig_inclusion NeSyPatterns s = return . inclusionMap s
          signature_union NeSyPatterns = sigUnion
          symbol_to_raw NeSyPatterns = symbolToRaw
          id_to_raw NeSyPatterns = idToRaw
          matches NeSyPatterns = Symbol.matches
          stat_symb_items NeSyPatterns = mkStatSymbItems
          stat_symb_map_items NeSyPatterns = mkStatSymbMapItem
          morphism_union NeSyPatterns = morphismUnion
          induced_from_morphism NeSyPatterns = inducedFromMorphism
          induced_from_to_morphism NeSyPatterns = inducedFromToMorphism
          signature_colimit NeSyPatterns = signatureColimit
#ifdef UNI_PACKAGE
          theory_to_taxonomy NeSyPatterns = nesy2Tax
#endif

-- | Sublogics
