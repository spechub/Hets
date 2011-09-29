{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the common logic
-}

module CommonLogic.Logic_CommonLogic where

import Logic.Logic

import ATC.ProofTree ()
import Common.ProofTree

import CommonLogic.ATC_CommonLogic ()
import CommonLogic.Sign
import CommonLogic.AS_CommonLogic
import CommonLogic.Symbol as Symbol
import CommonLogic.Analysis
import CommonLogic.Parse_CLIF
import CommonLogic.Parse_Symbols
import CommonLogic.Morphism

import qualified Data.Map as Map

import CommonLogic.OMDocExport
import CommonLogic.OMDocImport as OMDocImport
import CommonLogic.OMDoc
import CommonLogic.Sublogic

data CommonLogic = CommonLogic deriving Show

instance Language CommonLogic where
    description _ = "CommonLogic Logic\n"
        ++ ""

instance Category Sign Morphism
    where
      ide = idMor
      dom = source
      cod = target
      isInclusion = Map.null . propMap
      legal_mor = isLegalMorphism
      composeMorphisms = composeMor

instance Sentences CommonLogic
    TEXT_MRS
    Sign
    Morphism
    Symbol
    where
      negation CommonLogic = Just . negForm
      sym_of CommonLogic = singletonList . symOf
      symmap_of CommonLogic = getSymbolMap -- returns the symbol map
      sym_name CommonLogic = getSymbolName -- returns the name of a symbol
      map_sen CommonLogic = mapSentence -- TODO

instance Syntax CommonLogic
    BASIC_SPEC
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    where
      parse_basic_spec CommonLogic = Just basicSpec
      parse_symb_items CommonLogic = Just symbItems
      parse_symb_map_items CommonLogic = Just symbMapItems

instance Logic CommonLogic
    CommonLogicSL     -- Sublogics
    BASIC_SPEC        -- basic_spec
    TEXT_MRS          -- sentence
    SYMB_ITEMS        -- symb_items
    SYMB_MAP_ITEMS    -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ProofTree         -- proof_tree
    where
       all_sublogics CommonLogic = sublogics_all
       empty_proof_tree CommonLogic = emptyProofTree
       provers CommonLogic = []
       omdoc_metatheory CommonLogic = Just clMetaTheory
       export_senToOmdoc CommonLogic = exportSenToOmdoc
       export_symToOmdoc CommonLogic = exportSymToOmdoc
       omdocToSen CommonLogic = OMDocImport.omdocToSen
       omdocToSym CommonLogic = OMDocImport.omdocToSym


instance StaticAnalysis CommonLogic
    BASIC_SPEC
    TEXT_MRS
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    Sign
    Morphism
    Symbol
    Symbol
    where
      basic_analysis CommonLogic = Just basicCommonLogicAnalysis
      empty_signature CommonLogic = emptySig
      is_subsig CommonLogic = isSubSigOf
      subsig_inclusion CommonLogic s = return . inclusionMap s
      signature_union CommonLogic = sigUnion
      symbol_to_raw CommonLogic = symbolToRaw
      id_to_raw CommonLogic = idToRaw
      matches CommonLogic = Symbol.matches
      induced_from_morphism CommonLogic = inducedFromMorphism
      add_symb_to_sign CommonLogic = addSymbToSign -- TODO

{-
      stat_symb_items CommonLogic = ()
      stat_symb_map_items CommonLogic = ()
      morphism_union CommonLogic = ()
      signature_colimit CommonLogic = ()
-}

-- | Sublogics
instance SemiLatticeWithTop CommonLogicSL where
    join = sublogics_max
    top = CommonLogic.Sublogic.top

instance MinSublogic CommonLogicSL BASIC_SPEC where
     minSublogic = sl_basic_spec bottom

instance MinSublogic CommonLogicSL Sign where
    minSublogic = sl_sig bottom

instance SublogicName CommonLogicSL where
    sublogicName = sublogics_name

instance MinSublogic CommonLogicSL TEXT_MRS where
    minSublogic (Text_mrs (t,_)) = sublogic_text bottom t

instance MinSublogic CommonLogicSL NAME where
    minSublogic = sublogic_name bottom

instance MinSublogic CommonLogicSL Symbol where
    minSublogic = sl_sym bottom

instance MinSublogic CommonLogicSL Morphism where
    minSublogic = sl_mor bottom

instance MinSublogic CommonLogicSL SYMB_MAP_ITEMS where
    minSublogic = sl_symmap bottom

instance MinSublogic CommonLogicSL SYMB_ITEMS where
    minSublogic = sl_symitems bottom

instance ProjectSublogic CommonLogicSL BASIC_SPEC where
  projectSublogic = prBasicSpec

instance ProjectSublogicM CommonLogicSL NAME where
  projectSublogicM = prName

instance ProjectSublogicM CommonLogicSL SYMB_MAP_ITEMS where
  projectSublogicM = prSymMapM

instance ProjectSublogicM CommonLogicSL SYMB_ITEMS where
  projectSublogicM = prSymItemsM

instance ProjectSublogic CommonLogicSL Sign where
  projectSublogic = prSig

instance ProjectSublogic CommonLogicSL Morphism where
  projectSublogic = prMor

instance ProjectSublogicM CommonLogicSL Symbol where
  projectSublogicM = prSymbolM
