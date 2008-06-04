{- |
Module      :  $Header$
Description :  Symbols for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Symbol (
    Symbol,
    toId,
    fromSign,
    fromMorphism
) where

import Maude.Meta
import Maude.Sign
import Maude.Morphism

import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Common.Id as Id

type Symbol = Qid

toId :: Symbol -> Id.Id
toId = qid

fromSign :: Sign -> Set.Set Symbol
fromSign sign = Set.unions [(sorts sign), (opNames sign), (labels sign)]

fromMorphism :: Morphism -> Map.Map Symbol Symbol
fromMorphism mor = Map.unions [(sortMap mor), (opMap mor), (labelMap mor)]
