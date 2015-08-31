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

import ATC.ProofTree ()

import Common.ProofTree

import CommonLogic.ATC_CommonLogic ()
import CommonLogic.Sign
import CommonLogic.AS_CommonLogic
import CommonLogic.Symbol as Symbol
import CommonLogic.Analysis
import qualified CommonLogic.Parse_CLIF as CLIF
import qualified CommonLogic.Parse_KIF as KIF
import qualified CommonLogic.Print_KIF as Print_KIF
import CommonLogic.Morphism
import CommonLogic.OMDocExport
import CommonLogic.OMDocImport as OMDocImport
import CommonLogic.OMDoc
import CommonLogic.Sublogic

import qualified Data.Map as Map
import Data.Monoid

import Logic.Logic

data CommonLogic = CommonLogic deriving Show

instance Language CommonLogic where
    description _ = "CommonLogic Logic\n"

instance Category Sign Morphism
    where
      ide = idMor
      dom = source
      cod = target
      isInclusion = Map.null . propMap
      legal_mor = isLegalMorphism
      composeMorphisms = composeMor

instance Sentences CommonLogic
    TEXT_META
    Sign
    Morphism
    Symbol
    where
      negation CommonLogic = Just . negForm
      sym_of CommonLogic = singletonList . symOf
      symmap_of CommonLogic = getSymbolMap -- returns the symbol map
      sym_name CommonLogic = getSymbolName -- returns the name of a symbol
      map_sen CommonLogic = mapSentence -- TODO
      symsOfSen CommonLogic = symsOfTextMeta
      symKind CommonLogic = Symbol.symKind

instance Monoid BASIC_SPEC where
    mempty = Basic_spec []
    mappend (Basic_spec l1) (Basic_spec l2) = Basic_spec $ l1 ++ l2

instance Syntax CommonLogic
    BASIC_SPEC
    Symbol
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    where
      parsersAndPrinters CommonLogic =
        addSyntax "KIF" (KIF.basicSpec, Print_KIF.printBasicSpec)
        $ addSyntax "CLIF" (CLIF.basicSpec, pretty)
        $ makeDefault (CLIF.basicSpec, pretty)
      parse_symb_items CommonLogic = Just CLIF.symbItems
      parse_symb_map_items CommonLogic = Just CLIF.symbMapItems

instance Logic CommonLogic
    CommonLogicSL     -- Sublogics
    BASIC_SPEC        -- basic_spec
    TEXT_META         -- sentence
    SYMB_ITEMS        -- symb_items
    SYMB_MAP_ITEMS    -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ProofTree         -- proof_tree
    where
       stability CommonLogic = Testing
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
    TEXT_META
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
      stat_symb_items CommonLogic _ = mkStatSymbItems
      stat_symb_map_items CommonLogic _ _ = mkStatSymbMapItem
      induced_from_morphism CommonLogic = inducedFromMorphism
      induced_from_to_morphism CommonLogic = inducedFromToMorphism
      add_symb_to_sign CommonLogic = addSymbToSign -- TODO

{-
      stat_symb_items CommonLogic = ()
      stat_symb_map_items CommonLogic = ()
      morphism_union CommonLogic = ()
-}
      signature_colimit CommonLogic = signColimit


-- | Sublogics
instance SemiLatticeWithTop CommonLogicSL where
    lub = sublogics_max
    top = CommonLogic.Sublogic.top

instance MinSublogic CommonLogicSL BASIC_SPEC where
     minSublogic = sl_basic_spec bottom

instance MinSublogic CommonLogicSL Sign where
    minSublogic = sl_sig bottom

instance SublogicName CommonLogicSL where
    sublogicName = sublogics_name

instance MinSublogic CommonLogicSL TEXT_META where
    minSublogic tm = sublogic_text bottom $ getText tm

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
