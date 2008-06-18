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

import Maude.Meta

import Data.Typeable (Typeable)

-- for ShATermConvertible
import Common.ATerm.Conversion
-- for Pretty
import Common.DocUtils (Pretty(..))
import qualified Common.Doc as Doc


data Sentence = MembAx MembAx
              | Equation Equation
    deriving (Show, Eq, Ord, Typeable)

-- TODO: Add real pretty-printing for Maude Sentences.
instance Pretty Sentence where
    pretty _ = Doc.empty

-- TODO: Replace dummy implementation for ShATermConvertible Sentence.
instance ShATermConvertible Sentence where
    toShATermAux table _ = return (table, 0)
    fromShATermAux _ table = (table, error "Nope...")


instance HasSorts Sentence where
    getSorts sen = case sen of
        MembAx mb   -> getSorts mb
        Equation eq -> getSorts eq
    mapSorts mp sen = case sen of
        MembAx mb   -> MembAx (mapSorts mp mb)
        Equation eq -> Equation (mapSorts mp eq)

instance HasOps Sentence where
    getOps sen = case sen of
        MembAx mb   -> getOps mb
        Equation eq -> getOps eq
    mapOps mp sen = case sen of
        MembAx mb   -> MembAx (mapOps mp mb)
        Equation eq -> Equation (mapOps mp eq)

instance HasLabels Sentence where
    getLabels sen = case sen of
        MembAx mb   -> getLabels mb
        Equation eq -> getLabels eq
    mapLabels mp sen = case sen of
        MembAx mb   -> MembAx (mapLabels mp mb)
        Equation eq -> Equation (mapLabels mp eq)
