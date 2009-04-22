{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the propositional logic
   Also the instances for Syntax and Category.
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Logic_Propositional where

import Logic.Logic

import Propositional.Sign
import Propositional.Morphism
import Propositional.AS_BASIC_Propositional
import Propositional.ATC_Propositional()
import Propositional.Symbol as Symbol
import Propositional.Parse_AS_Basic
import Propositional.Analysis
import Propositional.Sublogic as Sublogic

#ifdef UNI_PACKAGE
#ifdef TABULAR_PACKAGE
import Propositional.ProveWithTruthTable
#endif
import Propositional.Prove
import Propositional.Conservativity
import Propositional.ProveMinisat
#endif

import ATC.ProofTree ()
import Common.ProofTree
import Common.ProverTools
import Common.Consistency

import qualified Data.Map as Map

-- | Lid for propositional logic
data Propositional = Propositional deriving Show

instance Language Propositional where
    description _ = "Propositional Logic\n"
        ++ "for more information please refer to\n"
        ++ "http://en.wikipedia.org/wiki/Propositional_logic"

-- | Instance of Category for propositional logic
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

-- | Instance of Sentences for propositional logic
instance Sentences Propositional FORMULA
    Sign Morphism Symbol where
    -- returns the set of symbols
    sym_of Propositional = symOf
    -- returns the symbol map
    symmap_of Propositional = getSymbolMap
    -- returns the name of a symbol
    sym_name Propositional = getSymbolName
    -- translation of sentences along signature morphism
    map_sen Propositional = mapSentence
    -- there is nothing to leave out
    simplify_sen Propositional _ = simplify

-- | Syntax of Propositional logic
instance Syntax Propositional BASIC_SPEC
    SYMB_ITEMS SYMB_MAP_ITEMS where
         parse_basic_spec Propositional = Just basicSpec
         parse_symb_items Propositional = Just symbItems
         parse_symb_map_items Propositional = Just symbMapItems

-- | Instance of Logic for propositional logc
instance Logic Propositional
    PropSL                    -- Sublogics
    BASIC_SPEC                -- basic_spec
    FORMULA                   -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
    ProofTree                      -- proof_tree
    where
      stability Propositional     = Experimental
      top_sublogic Propositional  = Sublogic.top
      all_sublogics Propositional = sublogics_all
    -- supplied provers
      provers Propositional = []
#ifdef UNI_PACKAGE
        ++ unsafeProverCheck "zchaff" "PATH" zchaffProver
        ++ unsafeProverCheck "minisat" "PATH" minisatProver
#ifdef TABULAR_PACKAGE
        ++ [ttProver]
#endif
      cons_checkers Propositional = []
         ++ unsafeProverCheck "zchaff" "PATH" propConsChecker
         ++ unsafeProverCheck "minisat" "PATH" minisatConsChecker
#ifdef TABULAR_PACKAGE
         ++ [ttConsistencyChecker]
#endif
      conservativityCheck Propositional = []
          ++ unsafeProverCheck "sKizzo" "PATH"
             (ConservativityChecker "sKizzo" conserCheck)
#ifdef TABULAR_PACKAGE
          ++ [ConservativityChecker "Truth Tables" ttConservativityChecker]
#endif
#endif


-- | Static Analysis for propositional logic
instance StaticAnalysis Propositional
    BASIC_SPEC                -- basic_spec
    FORMULA                   -- sentence
    SYMB_ITEMS                -- symb_items
    SYMB_MAP_ITEMS            -- symb_map_items
    Sign                          -- sign
    Morphism                  -- morphism
    Symbol                      -- symbol
    Symbol                      -- raw_symbol
        where
          basic_analysis Propositional           =
              Just basicPropositionalAnalysis
          empty_signature Propositional          = emptySig
          is_subsig Propositional                = isSubSigOf
          subsig_inclusion Propositional s = return . inclusionMap s
          signature_union Propositional          = sigUnion
          symbol_to_raw Propositional            = symbolToRaw
          id_to_raw     Propositional            = idToRaw
          matches       Propositional            = Symbol.matches
          stat_symb_items Propositional          = mkStatSymbItems
          stat_symb_map_items Propositional      = mkStatSymbMapItem
          morphism_union Propositional           = morphismUnion
          induced_from_morphism Propositional    = inducedFromMorphism
          induced_from_to_morphism Propositional = inducedFromToMorphism
          signature_colimit Propositional  = signatureColimit

-- | Sublogics
instance SemiLatticeWithTop PropSL where
    join = sublogics_max
    top  = Sublogic.top

instance MinSublogic PropSL BASIC_SPEC where
     minSublogic = sl_basic_spec bottom

instance MinSublogic PropSL Sign where
    minSublogic = sl_sig bottom

instance SublogicName PropSL where
    sublogicName = sublogics_name

instance MinSublogic PropSL FORMULA where
    minSublogic = sl_form bottom

instance MinSublogic PropSL Symbol where
    minSublogic = sl_sym bottom

instance MinSublogic PropSL SYMB_ITEMS where
    minSublogic = sl_symit bottom

instance MinSublogic PropSL Morphism where
    minSublogic = sl_mor bottom

instance MinSublogic PropSL SYMB_MAP_ITEMS where
    minSublogic = sl_symmap bottom

instance ProjectSublogicM PropSL Symbol where
    projectSublogicM = prSymbolM

instance ProjectSublogic PropSL Sign where
    projectSublogic = prSig

instance ProjectSublogic PropSL Morphism where
    projectSublogic = prMor

instance ProjectSublogicM PropSL SYMB_MAP_ITEMS where
    projectSublogicM = prSymMapM

instance ProjectSublogicM PropSL SYMB_ITEMS where
    projectSublogicM = prSymM

instance ProjectSublogic PropSL BASIC_SPEC where
    projectSublogic = prBasicSpec

instance ProjectSublogicM PropSL FORMULA where
    projectSublogicM = prFormulaM
