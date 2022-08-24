{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  ./RelationalScheme/Logic_Rel.hs
Description :  Instance of class Logic for Rel
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for RelationalSchemes
-}

module RelationalScheme.Logic_Rel where

import Common.DocUtils
import Common.Id

import Data.Monoid ()
import qualified Data.Set as Set

import Logic.Logic

import RelationalScheme.AS
import RelationalScheme.Sign
import RelationalScheme.ParseRS
import RelationalScheme.ATC_RelationalScheme ()
import RelationalScheme.StaticAnalysis

data RelScheme = RelScheme deriving (Show)

instance Language RelScheme where
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
instance Sentences RelScheme Sentence Sign RSMorphism RSSymbol where
    -- there is nothing to leave out
    simplify_sen RelScheme _ form = form
    print_named _ = printAnnoted pretty . fromLabelledSen
    map_sen RelScheme = map_rel
    symKind RelScheme = show . pretty . sym_kind

instance Semigroup RSRelationships where
    (RSRelationships l1 r1) <> (RSRelationships l2 r2) =
        RSRelationships (l1 ++ l2) $ appRange r1 r2
instance Monoid RSRelationships where
    mempty = RSRelationships [] nullRange

instance Semigroup RSTables where
    (RSTables s1) <> (RSTables s2) = RSTables $ Set.union s1 s2
instance Monoid RSTables where
    mempty = emptyRSSign

instance Semigroup RSScheme where
    (RSScheme l1 s1 r1) <> (RSScheme l2 s2 r2) = RSScheme
      (l1 <> l2) (s1 <> s2) $ appRange r1 r2
instance Monoid RSScheme where
    mempty = RSScheme mempty mempty nullRange

-- | Syntax of Rel
instance Syntax RelScheme RSScheme RSSymbol () () where
         parse_basic_spec RelScheme = Just parseRSScheme
         parse_symb_items _ = Nothing
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
      stability RelScheme = Experimental

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
      basic_analysis RelScheme = Just basic_Rel_analysis
      empty_signature RelScheme = emptyRSSign
      is_subsig RelScheme = isRSSubsig
      subsig_inclusion RelScheme = rsInclusion
      signature_union RelScheme = uniteSig
