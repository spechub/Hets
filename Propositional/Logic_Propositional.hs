{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  ./Propositional/Logic_Propositional.hs
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

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

import ATC.ProofTree ()

import Logic.Logic

import Propositional.Sign
import Propositional.Morphism
import Propositional.AS_BASIC_Propositional
import Propositional.ATC_Propositional ()
import Propositional.Fold
import Propositional.Symbol as Symbol
import Propositional.Parse_AS_Basic
import Propositional.Analysis
import Propositional.Sublogic as Sublogic
import Propositional.ProveWithTruthTable
import Propositional.Prove
import Propositional.Conservativity
import Propositional.ProveMinisat

import Common.ProverTools
import Common.Consistency
import Common.ProofTree
import Common.Id

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Monoid ()

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
    negation Propositional = Just . negForm nullRange
    -- returns the set of symbols
    sym_of Propositional = singletonList . symOf
    -- returns the symbol map
    symmap_of Propositional = getSymbolMap
    -- returns the name of a symbol
    sym_name Propositional = getSymbolName
    symKind Propositional _ = "prop"
    -- translation of sentences along signature morphism
    map_sen Propositional = mapSentence
    -- there is nothing to leave out
    simplify_sen Propositional _ = simplify
    -- symbols of a sentence
    symsOfSen Propositional = pSymsOfSen
    -- test nominals
    is_nominal_sen Propositional noms aSen = 
     case aSen of
      Predication p ->
        let pId = simpleIdToId p 
        in if Set.member pId noms then (True, Just pId) else (False, Nothing)
      _ -> (False, Nothing)

instance Semigroup BASIC_SPEC where
    (Basic_spec l1) <> (Basic_spec l2) = Basic_spec $ l1 ++ l2
instance Monoid BASIC_SPEC where
    mempty = Basic_spec []

-- - | Syntax of Propositional logic
instance Syntax Propositional BASIC_SPEC
    Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
         parsersAndPrinters Propositional =
           addSyntax "Hets" (basicSpec, pretty)
           $ makeDefault (basicSpec, pretty)
         parse_symb_items Propositional = Just . const $ symbItems
         parse_symb_map_items Propositional = Just . const $ symbMapItems

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
        -- hybridization
      parse_basic_sen Propositional = Just $ const impFormula
      parse_formula Propositional = Just $ impFormula
      parse_prim_formula Propositional = Just $ const primFormula
      stability Propositional = Stable
      top_sublogic Propositional = Sublogic.top
      all_sublogics Propositional = sublogics_all
      empty_proof_tree Propositional = emptyProofTree
    -- supplied provers
      provers Propositional =
        [zchaffProver, minisatProver Minisat, minisatProver Minisat2, ttProver]
      cons_checkers Propositional =
        [ propConsChecker, minisatConsChecker Minisat
        , minisatConsChecker Minisat2, ttConsistencyChecker]
      conservativityCheck Propositional =
          [ ConservativityChecker "sKizzo" (checkBinary "sKizzo") conserCheck
          , ConservativityChecker "Truth Tables" (return Nothing)
              ttConservativityChecker]
      -- helpers for generic hyridization
      sublogicsTypeName Propositional = ("PropSL","Propositional.Sublogic")
      basicSpecTypeName Propositional = ("BASIC_SPEC","Propositional.AS_BASIC_Propositional")
      sentenceTypeName Propositional = ("FORMULA","Propositional.AS_BASIC_Propositional")
      symbItemsTypeName Propositional = ("SYMB_ITEMS","Propositional.AS_BASIC_Propositional")
      symbMapItemsTypeName Propositional = ("SYMB_MAP_ITEMS","Propositional.AS_BASIC_Propositional")
      signTypeName Propositional = ("Sign","Propositional.Sign")
      morphismTypeName Propositional = ("Morphism","Propositional.Morphism")
      symbolTypeName Propositional = ("Symbol","Propositional.Symbol")
      rawSymbolTypeName Propositional = ("Symbol","Propositional.Symbol")
      proofTreeTypeName Propositional = ("ProofTree","Common.ProofTree")
      constr_to_sens Propositional = constrToSens

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
          basic_analysis Propositional =
              Just basicPropositionalAnalysis
          sen_analysis Propositional = Just pROPsen_analysis
          add_symb_to_sign Propositional = addSymbToSign
          empty_signature Propositional = emptySig
          is_subsig Propositional = isSubSigOf
          subsig_inclusion Propositional s = return . inclusionMap s
          signature_union Propositional = sigUnion
          symbol_to_raw Propositional = symbolToRaw
          raw_to_symbol Propositional = rawToSymbol
          id_to_raw Propositional = idToRaw
          matches Propositional = Symbol.matches
          stat_symb_items Propositional _ = mkStatSymbItems
          stat_symb_map_items Propositional _ _ = mkStatSymbMapItem
          morphism_union Propositional = morphismUnion
          induced_from_morphism Propositional = inducedFromMorphism
          induced_from_to_morphism Propositional = inducedFromToMorphism
          signature_colimit Propositional = signatureColimit
          

-- | Sublogics
instance SemiLatticeWithTop PropSL where
    lub = sublogics_max
    top = Sublogic.top

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
