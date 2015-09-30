{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for Rel
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for EVTs
-}

module EVT.Logic_Rel where

import Common.DocUtils
import Common.Id

import Data.Monoid
import qualified Data.Set as Set

import Logic.Logic

import EVT.AS
import EVT.Sign
import EVT.ParseRS
import EVT.ATC_EVT ()
import EVT.StaticAnalysis

data Evt = Evt deriving (Show)

instance Language Evt where
    description _ =
        "Simple logic for Relational Schemes"

-- | Instance of Category for Rel
instance Category
        Sign                   -- sign
        RSMorphism             -- mor
        where
                dom = domain
                cod = codomain
                ide = idMor
                composeMorphisms = comp_rst_mor

-- | Instance of Sentences for Rel
instance Sentences Evt Sentence Sign RSMorphism RSSymbol where
    -- there is nothing to leave out
    simplify_sen Evt _ form = form
    print_named _ = printAnnoted pretty . fromLabelledSen
    map_sen Evt = map_rel

instance Monoid RSRelationships where
    mempty = RSRelationships [] nullRange
    mappend (RSRelationships l1 r1) (RSRelationships l2 r2) =
        RSRelationships (l1 ++ l2) $ appRange r1 r2

instance Monoid RSTables where
    mempty = emptyRSSign
    mappend (RSTables s1) (RSTables s2) = RSTables $ Set.union s1 s2

instance Monoid RSScheme where
    mempty = RSScheme mempty mempty nullRange
    mappend (RSScheme l1 s1 r1) (RSScheme l2 s2 r2) = RSScheme
      (mappend l1 l2) (mappend s1 s2) $ appRange r1 r2

-- | Syntax of Rel
instance Syntax Evt RSScheme RSSymbol () () where
         parse_basic_spec Evt = Just parseRSScheme
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- | Instance of Logic for Relational Schemes
instance Logic Evt
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
      stability Evt = Experimental

-- | Static Analysis for Rel
instance StaticAnalysis Evt
    RSScheme                      -- basic_spec
    Sentence                      -- sentence
    ()                            -- symb_items
    ()                            -- symb_map_items
    Sign                          -- sign
    RSMorphism                    -- morphism
    RSSymbol                      -- symbol
    RSRawSymbol                   -- raw_symbol
    where
      basic_analysis Evt = Just basic_Rel_analysis
      empty_signature Evt = emptyRSSign
      is_subsig Evt = isRSSubsig
      subsig_inclusion Evt = rsInclusion
      signature_union Evt = uniteSig
