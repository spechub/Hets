{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for DL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for a description logic
	based on the Manchester syntax
-}

module DL.Logic_DL where

import Logic.Logic
import DL.ParseDL
import DL.AS
import Data.Set as Set()
import DL.ATC_DL
import DL.StaticAnalysis
import DL.Sign

data DL = DL deriving (Show)

instance Language DL where
    description _ =
        "Description Logic DL\n"++
         "This logic is designed to implement a human"++
         "readable syntax that is similar to Manchester Syntax"
         
-- | Instance of Category for DL
instance Category DL () () 
    
-- | Instance of Sentences for DL
instance Sentences DL DLBasicItem
    () () () where
    -- there is nothing to leave out
    simplify_sen DL _ form = form

-- | Syntax of DL
instance Syntax DL DLBasic
    () () where
         parse_basic_spec DL = Just csbsParse
         parse_symb_items _  = Nothing
         parse_symb_map_items _ = Nothing 

-- | Instance of Logic for DL
instance Logic DL
    ()                     -- Sublogics
    DLBasic                -- basic_spec
    DLBasicItem            -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    ()                     -- sign
    ()                     -- morphism
    ()                     -- symbol
    ()                     -- raw_symbol
    ()                     -- proof_tree
    where
      stability DL     = Experimental
      
-- | Static Analysis for DL
instance StaticAnalysis DL
    DLBasic                       -- basic_spec
    DLBasicItem                   -- sentence
    ()                            -- symb_items
    ()                            -- symb_map_items
    ()                            -- sign
    ()                            -- morphism
    ()                            -- symbol
    ()                            -- raw_symbol
    where
    basic_analysis DL = Just basic_DL_analysis
    is_subsig DL _ _ = True
    empty_signature DL = ()
    inclusion DL _ _ = 
        do
          return ()
