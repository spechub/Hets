{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./LF/Logic_LF.hs
Description :  Instances of classes defined in Logic.hs for the Edinburgh
               Logical Framework
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module LF.Logic_LF where

import LF.AS
import LF.Parse
import LF.MorphParser (readMorphism)
import LF.Sign
import LF.Morphism
import LF.ATC_LF ()
import LF.Analysis
import LF.Framework
import LF.ComorphFram ()

import Logic.Logic

import Common.Result
import Common.ExtSign

import qualified Data.Map as Map
import Data.Monoid

data LF = LF deriving Show

instance Language LF where
   description LF = "Edinburgh Logical Framework"

instance Category Sign Morphism where
   ide = idMorph
   dom = source
   cod = target
   composeMorphisms = compMorph
   isInclusion = Map.null . symMap . canForm

instance Semigroup BASIC_SPEC where
    (Basic_spec l1) <> (Basic_spec l2) = Basic_spec $ l1 ++ l2
instance Monoid BASIC_SPEC where
    mempty = Basic_spec []

instance Syntax LF BASIC_SPEC Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
   parse_basic_spec LF = Just basicSpec
   parse_symb_items LF = Just symbItems
   parse_symb_map_items LF = Just symbMapItems

instance Sentences LF
   Sentence
   Sign
   Morphism
   Symbol
   where
   map_sen LF m = Result [] . translate m
   sym_of LF = singletonList . getSymbols
   symKind LF _ = "const"

instance Logic LF
   ()
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   RAW_SYM
   ()

instance StaticAnalysis LF
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   RAW_SYM
   where
   basic_analysis LF = Just basicAnalysis
   stat_symb_items LF _ = symbAnalysis
   stat_symb_map_items LF _ _ = symbMapAnalysis
   symbol_to_raw LF = symName
   matches LF s1 s2 =
     not (isSym s2) || symName s1 == s2
     -- expressions are checked manually or symbols match by name
   empty_signature LF = emptySig
   is_subsig LF = isSubsig
   subsig_inclusion LF = inclusionMorph
   signature_union LF = sigUnion
   intersection LF = sigIntersection
   generated_sign LF syms sig = do
     sig' <- genSig syms sig
     inclusionMorph sig' sig
   cogenerated_sign LF syms sig = do
     sig' <- coGenSig syms sig
     inclusionMorph sig' sig
   induced_from_to_morphism LF m (ExtSign sig1 _) (ExtSign sig2 _) =
     inducedFromToMorphism (translMapAnalysis m sig1 sig2) sig1 sig2
   induced_from_morphism LF m sig =
     inducedFromMorphism (renamMapAnalysis m sig) sig

instance LogicalFramework LF
   ()
   BASIC_SPEC
   Sentence
   SYMB_ITEMS
   SYMB_MAP_ITEMS
   Sign
   Morphism
   Symbol
   RAW_SYM
   ()
   where
   base_sig LF = baseSig
   write_logic LF = writeLogic
   write_syntax LF = writeSyntax
   write_proof LF = writeProof
   write_model LF = writeModel
   write_comorphism LF = writeComorphism
   read_morphism LF = readMorphism
