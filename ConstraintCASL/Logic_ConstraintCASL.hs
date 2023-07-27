{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./ConstraintCASL/Logic_ConstraintCASL.hs
Description :  instance of the class Logic for ConstraintCASL
Copyright   :  (c) Uni Bremen 2002-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for Constraint CASL.
   Also the instances for Syntax an Category.
-}

module ConstraintCASL.Logic_ConstraintCASL where

import Logic.Logic

import Common.DocUtils

import ConstraintCASL.AS_ConstraintCASL
import ConstraintCASL.Formula
import ConstraintCASL.StaticAna
import ConstraintCASL.ATC_ConstraintCASL ()
import ConstraintCASL.Print_AS ()

import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.ToDoc ()
import CASL.SymbolParser
import CASL.MapSentence
import CASL.ATC_CASL ()
import CASL.Sublogic
import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL

data ConstraintCASL = ConstraintCASL deriving Show

instance Language ConstraintCASL where
 description _ =
  "ConstraintCASL - a restriction of CASL to constraint "
  ++ "formulas over predicates"

instance Syntax ConstraintCASL ConstraintCASLBasicSpec
                Symbol SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec ConstraintCASL = Just $ basicSpec constraintKeywords
         parse_symb_items ConstraintCASL = Just . const $ symbItems []
         parse_symb_map_items ConstraintCASL = Just . const $ symbMapItems []

-- lattices (for sublogics) is missing

instance Sentences ConstraintCASL ConstraintCASLFORMULA
                   ConstraintCASLSign ConstraintCASLMor Symbol where
      map_sen ConstraintCASL m = return . mapSen (const id) m
      sym_of ConstraintCASL = symOf
      symKind ConstraintCASL = show . pretty . symbolKind . symbType
      symmap_of ConstraintCASL = morphismToSymbMap
      sym_name ConstraintCASL = symName

instance StaticAnalysis ConstraintCASL
               ConstraintCASLBasicSpec ConstraintCASLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               ConstraintCASLSign
               ConstraintCASLMor
               Symbol RawSymbol where
         basic_analysis ConstraintCASL = Just basicConstraintCASLAnalysis
         stat_symb_map_items ConstraintCASL = statSymbMapItems
         stat_symb_items ConstraintCASL = statSymbItems

         symbol_to_raw ConstraintCASL = symbolToRaw
         id_to_raw ConstraintCASL = idToRaw
         matches ConstraintCASL = CASL.Morphism.matches
         is_transportable ConstraintCASL = isSortInjective

         empty_signature ConstraintCASL = emptySign ()
         signature_union ConstraintCASL s = return . addSig const s
         morphism_union ConstraintCASL = plainMorphismUnion const
         final_union ConstraintCASL = finalUnion const
         is_subsig ConstraintCASL = isSubSig trueC
         subsig_inclusion ConstraintCASL = sigInclusion ()
         cogenerated_sign ConstraintCASL = cogeneratedSign ()
         generated_sign ConstraintCASL = generatedSign ()
         induced_from_morphism ConstraintCASL = inducedFromMorphism ()
         induced_from_to_morphism ConstraintCASL =
             inducedFromToMorphism () trueC const

instance MinSL () ConstraintFORMULA where
    minSL _ = bottom

instance ProjForm () ConstraintFORMULA where
    projForm _ = Just . ExtFORMULA

instance Logic ConstraintCASL CASL_Sublogics
               ConstraintCASLBasicSpec ConstraintCASLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               ConstraintCASLSign
               ConstraintCASLMor
               Symbol RawSymbol () where

         stability _ = Experimental
         proj_sublogic_epsilon ConstraintCASL = pr_epsilon ()
         all_sublogics _ = sublogics_all [()]
         empty_proof_tree _ = ()
