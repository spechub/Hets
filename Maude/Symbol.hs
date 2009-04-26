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

import Data.Set (Set)
import Data.Map (Map)

import Common.Id (Id)


type Symbol = Qid
type SymbolSet = Set Symbol
type SymbolMap = Map Symbol Symbol

toId :: Symbol -> Id
toId = qid
