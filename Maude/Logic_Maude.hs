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

-- | Lid for Maude
data Maude = Maude
    deriving (Show, Eq)

instance Language Maude where
    description _ = unlines
        [ "Maude - A High-Performance Rewriting Logic Framework"
        , "This logic is rewriting logic, a logic of concurrent change that"
        , " can naturally deal with state and with concurrent computations."
        , "For an overview of Maude see <http://maude.cs.uiuc.edu/overview.html>."
        , "For an information on rewriting logic see <http://maude.cs.uiuc.edu/rwl.html>."
        , "For anything else about the Maude project see <http://maude.cs.uiuc.edu/>." ]

-- | Instance of Category for Maude
instance Category Maude Sign.Sign Morphism.Morphism where
    ide Maude = Morphism.identity
    dom Maude = Morphism.source
    cod Maude = Morphism.target
    comp Maude = Morphism.compose
    legal_obj Maude = Sign.isLegal
    legal_mor Maude = Morphism.isLegal

-- TODO: Complete the instance definition.
---- | Instance of Sentences for Maude
--instance Sentences Maude () Sign.Sign Morphism.Morphism Symbol.Symbol where
--    ---- symbols ----
--    sym_name Maude = Symbol.toId
--    sym_of Maude = Symbol.fromSign
--    symmap_of Maude = Symbol.fromMorphism
