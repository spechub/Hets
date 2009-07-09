{- |
Module      :  $Header$
Description :  Sentences for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of sentences for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Sentence (
    Sentence(..),
) where

import Maude.AS_Maude


data Sentence = Membership Membership
              | Equation Equation
              -- We are excluding Rules for now.
    deriving (Show, Read)
