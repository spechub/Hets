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
    SymbolSet,
    SymbolMap,
    toId,
) where

import Maude.Meta

import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Id (Id)

type Symbol    = Qid
type SymbolSet = Set.Set Symbol
type SymbolMap = Map.Map Symbol Symbol

toId :: Symbol -> Id
toId = qid
