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

import Common.DefaultMorphism
import Common.Id as Id

import Logic.Logic

import ATC.ProofTree ()

import CommonLogic.ATC_CommonLogic ()
import CommonLogic.Sign
import CommonLogic.AS_CommonLogic
import CommonLogic.Symbol
import CommonLogic.Analysis

data CommonLogic = CommonLogic deriving Show

instance Language CommonLogic where
    description _ = "CommonLogic Logic\n"
        ++ ""

type Morphism = DefaultMorphism Sign

instance GetRange SENTENCE

instance Sentences CommonLogic
    SENTENCE
    Sign
    Morphism
    Symbol

instance Syntax CommonLogic
    [SENTENCE]
    ()
    ()

instance Logic CommonLogic
    ()                -- Sublogics
    [SENTENCE]        -- basic_spec
    SENTENCE          -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    Symbol            -- symbol
    Symbol            -- raw_symbol
    ()                -- proof_tree

instance StaticAnalysis CommonLogic
    [SENTENCE]
    SENTENCE
    ()
    ()
    Sign
    Morphism
    Symbol
    Symbol
    where
      basic_analysis CommonLogic    = Just basicCommonLogicAnalysis
      empty_signature CommonLogic   = emptySig
      is_subsig CommonLogic         = isSubSigOf
