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
    Symbol(..),
    SymbolSet,
    SymbolMap,
    toId,
) where

import Maude.AS_Maude
import Maude.Printing

import Data.Set (Set)
import Data.Map (Map)

import Common.Id (Id, mkId, GetRange, getRange, nullRange)

import qualified Common.Doc as Doc
import Common.DocUtils (Pretty(..))


data Symbol = Sort Qid
            | Lab Qid
            | Operator Qid [Qid] Qid
            deriving (Show, Ord, Eq)
type SymbolSet = Set Symbol
type SymbolMap = Map Symbol Symbol

instance Pretty Symbol where
  pretty (Sort q) = Doc.text $ "sort " ++ show q
  pretty (Lab q) = Doc.text $ "label " ++ show q
  pretty (Operator top ar co) = Doc.text $ "op " ++ show top ++ " : " ++
                                printArity ar ++ " -> " ++ show co ++ " ."

instance GetRange Symbol where
  getRange _ = nullRange

toQid :: Symbol -> Qid
toQid (Sort qid) = qid
toQid (Lab qid) = qid
toQid (Operator qid _ _) = qid

toId :: Symbol -> Id
toId = mkId . return . toQid
