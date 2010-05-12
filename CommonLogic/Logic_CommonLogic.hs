{- |
Module      :  $Header$
Description :  Instance of class Logic for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the common logic
-}

module CommonLogic.Logic_CommonLogic where

import Logic.Logic

import ATC.ProofTree ()

import CommonLogic.ATC_CommonLogic ()
import CommonLogic.Sign
import CommonLogic.AS_CommonLogic
import CommonLogic.Symbol
import CommonLogic.Analysis
import CommonLogic.Parse_CLIF
import CommonLogic.Morphism

data CommonLogic = CommonLogic deriving Show

instance Language CommonLogic where
    description _ = "CommonLogic Logic\n"
        ++ ""

instance Sentences CommonLogic
    SENTENCE
    Sign
    Morphism
    Symbol

instance Syntax CommonLogic
    BASIC_SPEC
    NAME
    () where
    parse_basic_spec CommonLogic = Just basicSpec
    parse_symb_items CommonLogic = Just symbItems
    -- parse_symb_map_items CommonLogic = Just symbMapItems

instance Logic CommonLogic
    ()                -- Sublogics
    BASIC_SPEC        -- basic_spec
    SENTENCE          -- sentence
    NAME                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ()                -- proof_tree

instance StaticAnalysis CommonLogic
    BASIC_SPEC
    SENTENCE
    NAME
    ()
    Sign
    Morphism
    Symbol
    Symbol
    where
      basic_analysis CommonLogic    = Just basicCommonLogicAnalysis
      empty_signature CommonLogic   = emptySig
      is_subsig CommonLogic         = isSubSigOf
      signature_union CommonLogic         = sigUnion
      
