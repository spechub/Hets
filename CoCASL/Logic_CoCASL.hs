{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for CoCASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Instance of class Logic for CoCASL.
-}

module CoCASL.Logic_CoCASL where

import CoCASL.AS_CoCASL
import CoCASL.ATC_CoCASL ()
import CoCASL.CoCASLSign
import CoCASL.Parse_AS
import CoCASL.StatAna
import CoCASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Logic_CASL
import CASL.MapSentence
import CASL.Morphism
import CASL.Parse_AS_Basic
import CASL.Sign
import CASL.Sublogic
import CASL.SymbolMapAnalysis
import CASL.SymbolParser
import Logic.Logic

data CoCASL = CoCASL deriving Show

instance Language CoCASL  where
 description _ =
  "CoCASL is the coalgebraic extension of CASL."

type CoCASLMor = Morphism C_FORMULA CoCASLSign (DefMorExt CoCASLSign)
type CoCASLFORMULA = FORMULA C_FORMULA

instance SignExtension CoCASLSign where
  isSubSignExtension = isSubCoCASLSign

instance Syntax CoCASL C_BASIC_SPEC SYMB_ITEMS SYMB_MAP_ITEMS where
    parse_basic_spec CoCASL = Just $ basicSpec cocasl_reserved_words
    parse_symb_items CoCASL = Just $ symbItems cocasl_reserved_words
    parse_symb_map_items CoCASL = Just $ symbMapItems cocasl_reserved_words

-- CoCASL logic

map_C_FORMULA :: MapSen C_FORMULA CoCASLSign (DefMorExt CoCASLSign)
map_C_FORMULA mor frm = case frm of
           BoxOrDiamond b m f ps -> let
              newF = mapSen map_C_FORMULA mor f
              newM = case m of
                   Simple_mod _ ->  m
                   Term_mod t -> Term_mod $ mapTerm map_C_FORMULA mor t
              in BoxOrDiamond b newM newF ps
           phi -> phi

instance Sentences CoCASL CoCASLFORMULA CSign CoCASLMor Symbol where
      map_sen CoCASL m = return . mapSen map_C_FORMULA m
      sym_of CoCASL = symOf
      symmap_of CoCASL = morphismToSymbMap
      sym_name CoCASL = symName

instance StaticAnalysis CoCASL C_BASIC_SPEC CoCASLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol where
         basic_analysis CoCASL = Just basicCoCASLAnalysis
         stat_symb_map_items CoCASL = statSymbMapItems
         stat_symb_items CoCASL = statSymbItems

         symbol_to_raw CoCASL = symbolToRaw
         id_to_raw CoCASL = idToRaw
         matches CoCASL = CASL.Morphism.matches

         empty_signature CoCASL = emptySign emptyCoCASLSign
         signature_union CoCASL s = return . addSig addCoCASLSign s
         intersection CoCASL s = return . interSig interCoCASLSign s
         morphism_union CoCASL = morphismUnion (const id) addCoCASLSign
         final_union CoCASL = finalUnion addCoCASLSign
         is_subsig CoCASL = isSubSig isSubCoCASLSign
         subsig_inclusion CoCASL = sigInclusion emptyMorExt
         cogenerated_sign CoCASL = cogeneratedSign emptyMorExt
         generated_sign CoCASL = generatedSign emptyMorExt
         induced_from_morphism CoCASL = inducedFromMorphism emptyMorExt
         induced_from_to_morphism CoCASL =
             inducedFromToMorphism emptyMorExt isSubCoCASLSign diffCoCASLSign

instance NameSL Bool where
    nameSL b = if b then "Co" else ""

instance MinSL Bool C_FORMULA where
    minSL = minFormSublogic

instance MinSL Bool C_SIG_ITEM where
    minSL = minCSigItem

instance MinSL Bool C_BASIC_ITEM where
    minSL = minCBaseItem

instance ProjForm Bool C_FORMULA where
    projForm _ = Just . ExtFORMULA

instance ProjSigItem Bool C_SIG_ITEM C_FORMULA where
    projSigItems _ s = (Just $ Ext_SIG_ITEMS s, [])

instance ProjBasic Bool C_BASIC_ITEM C_SIG_ITEM C_FORMULA where
    projBasicItems _ b = (Just $ Ext_BASIC_ITEMS b, [])

instance Logic CoCASL CoCASL_Sublogics
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               CoCASLMor
               Symbol RawSymbol () where
         stability CoCASL = Unstable
         proj_sublogic_epsilon CoCASL = pr_epsilon emptyMorExt
         all_sublogics CoCASL = sublogics_all [False, True]
         empty_proof_tree CoCASL = ()
