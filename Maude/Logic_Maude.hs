{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  ./Maude/Logic_Maude.hs
Description :  Instance of class Logic for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for Maude. See <http://maude.cs.uiuc.edu/>
-}

module Maude.Logic_Maude where

import Logic.Logic

import Common.DocUtils

import Maude.AS_Maude (MaudeText (..))
import Maude.Parse (mStuff)
import Maude.Symbol (Symbol)
import Maude.Sentence (Sentence)
import Maude.Sign (Sign)
import Maude.Morphism (Morphism)
import qualified Maude.Symbol as Symbol
import qualified Maude.Sign as Sign
import qualified Maude.Morphism as Morphism

import Maude.ATC_Maude ()

import Maude.Shellout

import Common.AS_Annotation
import Common.ExtSign

import Data.Monoid ()

import System.IO.Unsafe

-- | Lid for Maude
data Maude = Maude
           deriving (Show, Eq)


-- | Instance of Language for Maude
instance Language Maude where
    description _ = unlines
        [ "Maude - A High-Performance Rewriting Logic Framework"
        , "This logic is rewriting logic, a logic of concurrent change that"
        , "can naturally deal with state and with concurrent computations."
        , "For an overview of Maude see" ++
          " <http://maude.cs.uiuc.edu/overview.html>."
        , "For information about rewriting logic see" ++
          " <http://maude.cs.uiuc.edu/rwl.html>."
        , "For information about the Maude project see" ++
          " <http://maude.cs.uiuc.edu/>." ]


-- | Instance of Category for Maude
instance Category Sign Morphism where
    ide = Morphism.identity
    dom = Morphism.source
    cod = Morphism.target
    composeMorphisms = Morphism.compose
    inverse = Morphism.inverse
    isInclusion = Morphism.isInclusion
    legal_mor = Morphism.isLegal

-- | Instance of Sentences for Maude
instance Sentences Maude Sentence Sign Morphism Symbol where
    -- sentences --
    map_sen Maude = Morphism.translateSentence
    simplify_sen Maude = Sign.simplifySentence
    -- symbols --
    sym_name Maude = Symbol.toId
    symKind Maude = show . pretty . Symbol.sym_kind
    sym_of Maude = singletonList . Sign.symbols
    symmap_of Maude = Morphism.symbolMap

instance Semigroup MaudeText where
    (MaudeText l1) <> (MaudeText l2) = MaudeText
      . unlines $ lines l1 ++ lines l2
instance Monoid MaudeText where
    mempty = MaudeText ""

-- | Instance of Syntax for Maude
instance Syntax Maude MaudeText Symbol () () where
    parse_basic_spec Maude = Just (\ _ -> fmap MaudeText mStuff)
    {- parse_symb_items
    parse_symb_map_items -}

-- | Instance of StaticAnalysis for Maude
instance StaticAnalysis Maude
         MaudeText Sentence () () Sign Morphism Symbol Symbol
  where
    -- static analysis --
    basic_analysis Maude = let
        analyze (spec, sign, _) = let
            (rsig, sens) = unsafePerformIO $ basicAnalysis sign spec
            in return (spec, mkExtSign rsig, map (makeNamed "") sens)
        in Just analyze
    {- stat_symb_map_items
    stat_symb_items
    amalgamation --
    ensures_amalgamability
    signature_colimit
    qualify
    symbols and raw symbols --
    symbol_to_raw
    id_to_raw
    matches
    operations on signatures and morphisms -- -}
    is_subsig Maude = Sign.isSubsign
    empty_signature Maude = Sign.empty
    signature_union Maude sign1 sign2 = return $ Sign.union sign1 sign2
    intersection Maude sign1 sign2 = return $ Sign.intersection sign1 sign2
    -- final_union
    morphism_union Maude mor1 mor2 = return $ Morphism.union mor1 mor2
    subsig_inclusion Maude src tgt = return $ Morphism.inclusion src tgt
    {- generated_sign
    cogenerated_sign
    induced_from_morphism
    induced_from_to_morphism
    is_transportable
    is_injective
    theory_to_taxonomy -}

-- | Instance of Logic for Maude
instance Logic Maude
         () MaudeText Sentence () () Sign Morphism Symbol Symbol ()
  where
    stability Maude = Experimental
    {- data_logic
    top_sublogic
    all_sublogics
    proj_sublogic_epsilon
    provers --
    provers
    cons_checkers
    conservativityCheck -}
    empty_proof_tree Maude = ()

instance LogicalFramework Maude
         () MaudeText Sentence () () Sign Morphism Symbol Symbol ()
