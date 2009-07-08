{- |
Module      :  $Header$
Description :  Instance of class Logic for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for Maude. See <http://maude.cs.uiuc.edu/>
-}

=======

>>>>>>> .r11881
module Maude.Logic_Maude where

import Logic.Logic

import Maude.AS_Maude (MaudeText(..))
import Maude.Parse (mStuff)
import Maude.Sign     (Sign)
import Maude.Morphism (Morphism)
import Maude.Symbol   (Symbol)
import Maude.Sentence (Sentence)
import qualified Maude.Sign     as Sign
import qualified Maude.Morphism as Morphism
import qualified Maude.Symbol   as Symbol
import qualified Maude.Sentence as Sentence


-- | Lid for Maude
data Maude = Maude
    deriving (Show, Eq)


-- | Instance of Language for Maude
instance Language Maude where
    description _ = unlines
        [ "Maude - A High-Performance Rewriting Logic Framework"
        , "This logic is rewriting logic, a logic of concurrent change that"
        , " can naturally deal with state and with concurrent computations."
        , "For an overview of Maude see <http://maude.cs.uiuc.edu/overview.html>."
        , "For an information on rewriting logic see <http://maude.cs.uiuc.edu/rwl.html>."
        , "For anything else about the Maude project see <http://maude.cs.uiuc.edu/>." ]


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
    is_of_sign Maude = flip Sign.includesSentence
    map_sen Maude = Morphism.mapSentence
    simplify_sen Maude = Sign.simplifySentence
    -- parse_sentence Maude = Nothing
    -- print_sign Maude = pretty
    -- print_named Maude = printAnnoted (addBullet . pretty) . fromLabelledSen
    -- symbols --
    sym_name Maude = Symbol.toId
    sym_of Maude = Sign.symbols
    symmap_of Maude = Morphism.symbolMap


-- | Instance of Syntax for Maude
-- TODO: Implement real instance of Syntax for Maude
instance Syntax Maude MaudeText () () where
    parse_basic_spec Maude = Just $ fmap MaudeText mStuff
    -- parse_symb_items
    -- parse_symb_map_items

-- | Instance of StaticAnalysis for Maude
-- TODO: Implement real instance of StaticAnalysis for Maude
instance StaticAnalysis Maude MaudeText Sentence () () Sign Morphism Symbol
    Symbol where
    -- static analysis --
    -- basic_analysis
    -- stat_symb_map_items
    -- stat_symb_items
    -- amalgamation --
    -- ensures_amalgamability
    -- signature_colimit
    -- qualify
    -- symbols and raw symbols --
    -- symbol_to_raw
    -- id_to_raw
    -- matches
    -- operations on signatures and morphisms --
    empty_signature Maude = Sign.empty
    -- signature_union
    -- intersection
    -- final_union
    -- morphism_union
    -- is_subsig
    -- subsig_inclusion
    -- generated_sign
    -- cogenerated_sign
    -- induced_from_morphism
    -- induced_from_to_morphism
    -- is_transportable
    -- is_injective
    -- theory_to_taxonomy


-- | Instance of Logic for Maude
-- TODO: Implement real instance of Logic for Maude
instance Logic Maude () MaudeText Sentence () () Sign Morphism Symbol Symbol
    () where
    stability Maude = Experimental
    -- data_logic
    -- top_sublogic
    -- all_sublogics
    -- proj_sublogic_epsilon
    -- provers --
    -- provers
    -- cons_checkers
    -- conservativityCheck
    -- empty_proof_tree
