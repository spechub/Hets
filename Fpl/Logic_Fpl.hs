{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Fpl/Logic_Fpl.hs
Description :  logic instance for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

Instance of class Logic for FPL.
-}

module Fpl.Logic_Fpl where

import Logic.Logic

import Fpl.As
import Fpl.Sign
import Fpl.StatAna
import Fpl.Morphism
import Fpl.ATC_Fpl ()

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.SimplifySen
import CASL.SymbolParser
import CASL.Taxonomy
import CASL.Logic_CASL ()

import Common.DocUtils

data Fpl = Fpl deriving Show

instance Language Fpl where
  description _ = unlines
    [ "logic of functional programs (FPL) as CASL extension" ]

instance SignExtension SignExt where
  isSubSignExtension = isSubFplSign

instance Syntax Fpl FplBasicSpec Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec Fpl = Just $ basicSpec fplReservedWords
    parse_symb_items Fpl = Just . const $ symbItems fplReservedWords
    parse_symb_map_items Fpl = Just . const $ symbMapItems fplReservedWords

instance Sentences Fpl FplForm FplSign FplMor Symbol where
      map_sen Fpl m = return . mapFplSen m
      sym_of Fpl = symOf
      symKind Fpl = show . pretty . symbolKind . symbType
      symmap_of Fpl = morphismToSymbMap
      sym_name Fpl = symName
      simplify_sen Fpl = simplifySen minFplTerm simplifyTermExt . addBuiltins

instance StaticAnalysis Fpl FplBasicSpec FplForm
               SYMB_ITEMS SYMB_MAP_ITEMS
               FplSign
               FplMor
               Symbol RawSymbol where
         basic_analysis Fpl = Just basicFplAnalysis
         stat_symb_map_items Fpl = statSymbMapItems
         stat_symb_items Fpl = statSymbItems

         symbol_to_raw Fpl = symbolToRaw
         id_to_raw Fpl = idToRaw
         matches Fpl = CASL.Morphism.matches

         empty_signature Fpl = emptySign emptyFplSign
         signature_union Fpl s = return . addSig addFplSign s
         signatureDiff Fpl s = return . diffSig diffFplSign s
         intersection Fpl s = return . interSig interFplSign s
         morphism_union Fpl = plainMorphismUnion addFplSign
         final_union Fpl = finalUnion addFplSign
         is_subsig Fpl = isSubSig isSubFplSign
         subsig_inclusion Fpl = sigInclusion emptyMorExt
         cogenerated_sign Fpl = cogeneratedSign emptyMorExt
         generated_sign Fpl = generatedSign emptyMorExt
         induced_from_morphism Fpl = inducedFromMorphism emptyMorExt
         induced_from_to_morphism Fpl =
             inducedFromToMorphism emptyMorExt isSubFplSign diffFplSign
         theory_to_taxonomy Fpl = convTaxo

instance Logic Fpl ()
               FplBasicSpec FplForm SYMB_ITEMS SYMB_MAP_ITEMS
               FplSign
               FplMor
               Symbol RawSymbol () where
         stability _ = Experimental
         empty_proof_tree _ = ()
