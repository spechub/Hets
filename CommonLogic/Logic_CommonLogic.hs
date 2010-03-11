{- |
Module      :  $Header$
Description :  Instance of class Logic for common logic
Copyright   :  (c) Karl Luc, Uni Bremen 2010
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
    ()

instance Syntax CommonLogic
    [SENTENCE]
    ()
    ()

instance Logic CommonLogic
    ()                -- Sublogics
    [SENTENCE]               -- basic_spec
    SENTENCE          -- sentence
    ()                -- symb_items
    ()                -- symb_map_items
    Sign              -- sign
    Morphism          -- morphism
    ()                -- symbol
    ()                -- raw_symbol
    ()                -- proof_tree

instance StaticAnalysis CommonLogic
    [SENTENCE]
    SENTENCE
    ()
    ()
    (Sign)
    Morphism
    ()
    ()
    where
      empty_signature CommonLogic          = emptySig
