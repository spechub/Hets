{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
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
import Fpl.ATC_Fpl ()

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SimplifySen
import CASL.SymbolParser
import CASL.Taxonomy
import CASL.Logic_CASL ()

import Common.DocUtils

data Fpl = Fpl deriving Show

instance Language Fpl  where
 description _ = unlines
  [ "logic of functional programs (FPL) as CASL extension" ]

type FplSign = Sign TermExt SignExt
type FplMor = Morphism TermExt SignExt (DefMorExt SignExt)
type FplForm = FORMULA TermExt

instance SignExtension SignExt

instance Syntax Fpl FplBasicSpec SYMB_ITEMS SYMB_MAP_ITEMS where
    -- parse_basic_spec Fpl = Just $ basicSpec fplReservedWords
    parse_symb_items Fpl = Just $ symbItems fplReservedWords
    parse_symb_map_items Fpl = Just $ symbMapItems fplReservedWords

instance Sentences Fpl FplForm FplSign FplMor Symbol where
      sym_of Fpl = symOf
      symmap_of Fpl = morphismToSymbMap
      sym_name Fpl = symName
      print_sign Fpl = printSign pretty

instance StaticAnalysis Fpl FplBasicSpec FplForm
               SYMB_ITEMS SYMB_MAP_ITEMS
               FplSign
               FplMor
               Symbol RawSymbol where
         stat_symb_map_items Fpl = statSymbMapItems
         stat_symb_items Fpl = statSymbItems

         symbol_to_raw Fpl = symbolToRaw
         id_to_raw Fpl = idToRaw
         matches Fpl = CASL.Morphism.matches

         empty_signature Fpl = emptySign emptyFplSign
         signature_union Fpl s = return . addSig addFplSign s
         morphism_union Fpl = morphismUnion (const id) addFplSign
         final_union Fpl = finalUnion addFplSign
         is_subsig Fpl = isSubSig isSubFplSign
         subsig_inclusion Fpl = sigInclusion emptyMorExt
         cogenerated_sign Fpl = cogeneratedSign emptyMorExt
         generated_sign Fpl = generatedSign emptyMorExt
         induced_from_morphism Fpl = inducedFromMorphism emptyMorExt
         theory_to_taxonomy Fpl = convTaxo

instance Logic Fpl ()
               FplBasicSpec FplForm SYMB_ITEMS SYMB_MAP_ITEMS
               FplSign
               FplMor
               Symbol RawSymbol () where
         stability _ = Unstable
         empty_proof_tree _ = ()
