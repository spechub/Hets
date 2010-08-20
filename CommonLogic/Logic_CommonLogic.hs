{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  kluc@informatik.uni-bremen.de
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
import CommonLogic.Morphism

import qualified Data.Map as Map

-- import CommonLogic.OMDocExport
-- import CommonLogic.OMDocImport

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
    SENTENCE
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
    NAME
    SYMB_MAP_ITEMS
    where
      parse_basic_spec CommonLogic = Just basicSpec
      parse_symb_items CommonLogic = Nothing -- Just symbItems -- TODO
      parse_symb_map_items CommonLogic = Nothing -- Just symbMapItems -- TODO

instance Logic CommonLogic
    ()                -- Sublogics
    BASIC_SPEC        -- basic_spec
    SENTENCE          -- sentence
    NAME                -- symb_items
    SYMB_MAP_ITEMS     -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ProofTree                -- proof_tree
    where
       empty_proof_tree CommonLogic = emptyProofTree
       provers CommonLogic = []
{-
         omdoc_metatheory CommonLogic = Just clMetaTheory
         export_senToOmdoc CommonLogic = exportSenToOmdoc
         export_symToOmdoc CommonLogic = exportSymToOmdoc
         omdocToSen CommonLogic = omdocToSen
         omdocToSym CommonLogic = omdocToSym
-}

instance StaticAnalysis CommonLogic
    BASIC_SPEC
    SENTENCE
    NAME
    SYMB_MAP_ITEMS
    Sign
    Morphism
    Symbol
    Symbol
    where
      basic_analysis CommonLogic    = Just basicCommonLogicAnalysis
      empty_signature CommonLogic   = emptySig
      is_subsig CommonLogic         = isSubSigOf
      signature_union CommonLogic         = sigUnion
      symbol_to_raw CommonLogic = symbolToRaw
      id_to_raw CommonLogic = idToRaw
      matches CommonLogic = Symbol.matches
      induced_from_morphism CommonLogic = inducedFromMorphism -- TODO
      induced_from_to_morphism CommonLogic = inducedFromToMorphism -- TODO
      add_symb_to_sign CommonLogic = addSymbToSign -- TODO
{-
      stat_symb_items CommonLogic = ()
      stat_symb_map_items CommonLogic = ()
      morphism_union CommonLogic = ()
      signature_colimit CommonLogic = ()
-}
