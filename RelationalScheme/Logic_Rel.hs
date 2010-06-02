{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for Rel
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for RelationalSchemes
-}

module RelationalScheme.Logic_Rel where

import Logic.Logic
import RelationalScheme.AS
import RelationalScheme.Sign
import RelationalScheme.ParseRS
import RelationalScheme.ATC_RelationalScheme()
import RelationalScheme.StaticAnalysis
import Common.DocUtils

data RelScheme = RelScheme deriving (Show)

instance Language RelScheme where
    description _ =
        "Simple logic for Relational Schemes"

-- | Instance of Category for Rel
instance Category
        Sign                   -- sign
        RSMorphism             -- mor
        where
                legal_mor _  = False
                dom          = domain
                cod          = codomain
                ide          = idMor
                composeMorphisms = comp_rst_mor

-- ^ Instance of Sentences for Rel
instance Sentences RelScheme Sentence Sign RSMorphism RSSymbol where
    -- there is nothing to leave out
    simplify_sen RelScheme _ form = form
    print_named           _ = printAnnoted (pretty) . fromLabelledSen
    map_sen RelScheme             = map_rel

-- | Syntax of Rel
instance Syntax RelScheme RSScheme () () where
         parse_basic_spec RelScheme   = Just parseRSScheme
         parse_symb_items _     = Nothing
         parse_symb_map_items _ = Nothing

-- | Instance of Logic for Relational Schemes
instance Logic RelScheme
    ()                     -- Sublogics
    RSScheme               -- basic_spec
    Sentence               -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    Sign                   -- sign
    RSMorphism             -- morphism
    RSSymbol               -- symbol
    RSRawSymbol            -- raw_symbol
    ()                     -- proof_tree
    where
      stability RelScheme     = Experimental

-- | Static Analysis for Rel
instance StaticAnalysis RelScheme
    RSScheme                      -- basic_spec
    Sentence                      -- sentence
    ()                            -- symb_items
    ()                            -- symb_map_items
    Sign                          -- sign
    RSMorphism                    -- morphism
    RSSymbol                      -- symbol
    RSRawSymbol                   -- raw_symbol
    where
      basic_analysis RelScheme  = Just $ basic_Rel_analysis
      empty_signature RelScheme = emptyRSSign
      is_subsig RelScheme = isRSSubsig
      subsig_inclusion RelScheme = rsInclusion
      signature_union RelScheme = uniteSig
