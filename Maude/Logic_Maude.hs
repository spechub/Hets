{- |
Module      :  $Header$
Description :  Instance of class Logic for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for Maude.
    Also instances of Syntax and Category.
    ... sometime in the future, that is.
-}
{-
  Ref.

  ...
-}

module Maude.Logic_Maude where

import Logic.Logic

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
instance Category Sign.Sign Morphism.Morphism where
    ide = Morphism.identity
    dom = Morphism.source
    cod = Morphism.target
    comp = Morphism.compose
    -- isInclusion = \_ -> False -- TODO: implement Category.isInclusion.
    -- legal_obj = Sign.isLegal -- seems to be obsolete
    legal_mor = Morphism.isLegal


-- | Instance of Sentences for Maude
instance Sentences Maude Sentence.Sentence Sign.Sign Morphism.Morphism Symbol.Symbol where
    -- -- sentences -- --
    -- Uncommenting this signals a type error I don't understand...
    -- is_of_sign Maude = flip Sign.includesSentence
    map_sen Maude = Morphism.mapSentence
    -- -- | simplification of sentences (leave out qualifications)
    -- simplify_sen :: lid -> sign -> sentence -> sentence
    -- simplify_sen _ _ = id  -- default implementation
    -- simplify_sen Maude _ = id
    -- -- | parsing of sentences
    -- parse_sentence :: lid -> Maybe (AParser st sentence)
    -- parse_sentence _ = Nothing
    -- parse_sentence Maude = Nothing
    -- -- | print a sentence with comments
    -- print_named :: lid -> Named sentence -> Doc
    -- print_named _ = printAnnoted (addBullet . pretty) . fromLabelledSen
    -- -- symbols -- --
    sym_name Maude = Symbol.toId
    sym_of Maude = Sign.symbols
    symmap_of Maude = Morphism.symbolMap
