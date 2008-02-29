{-# OPTIONS -cpp #-}
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

data Rel = Rel deriving (Show)

instance Language Rel where
    description _ =
        "Simple logic for Relational Schemes"

-- | Instance of Category for Rel
instance Category
        Rel                    -- lid
        Sign                   -- sign
        RSMorphism             -- mor
        where
                legal_obj Rel _ = False
                legal_mor Rel _ = False
                dom       Rel = domain
                cod       Rel = codomain
                
-- ^ Instance of Sentences for Rel
instance Sentences Rel Sentence Sign RSMorphism () where
    -- there is nothing to leave out
    simplify_sen Rel _ form = form

-- | Syntax of Rel
instance Syntax Rel RSScheme () () where
         parse_basic_spec Rel   = Just parseRSScheme
         parse_symb_items _     = Nothing
         parse_symb_map_items _ = Nothing

-- | Instance of Logic for Relational Schemes
instance Logic Rel
    ()                     -- Sublogics
    RSScheme               -- basic_spec
    Sentence               -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    Sign                   -- sign
    RSMorphism             -- morphism
    ()                     -- symbol
    RSRawSymbol            -- raw_symbol
    ()                     -- proof_tree
    where
      stability Rel     = Experimental
      
-- | Static Analysis for Rel
instance StaticAnalysis Rel
    RSScheme                      -- basic_spec
    Sentence                      -- sentence
    ()                            -- symb_items
    ()                            -- symb_map_items
    Sign                          -- sign
    RSMorphism                    -- morphism
    ()                            -- symbol
    RSRawSymbol                   -- raw_symbol
    where
    basic_analysis Rel  = Just $ basic_Rel_analysis
    empty_signature Rel = emptyRSSign
    is_subsig Rel       = isRSSubsig

    
    