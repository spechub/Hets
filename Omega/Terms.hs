{- |
Module      :  $Header$
Description :  Hets-to-Omega conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

HasCASL terms will be exported to omega terms.
-}

module Omega.Terms
    ( toTerm
    ) where

import qualified Omega.DataTypes as DT

import HasCASL.FoldTerm
import HasCASL.As

toTerm :: Term -> String
toTerm = foldTerm toTermRec

toTermRec :: FoldRec String String
toTermRec = FoldRec
    { -- Term VarDecl
      foldQualVar = \t v -> show (t, v)
      -- Term -> OpBrand -> PolyId -> TypeScheme -> [Type] -> InstKind -> Range
    , foldQualOp = \t o i ts tp k r -> show (t, o, i, ts, tp, k, r)
    -- Term -> a -> a -> Range
    , foldApplTerm = \t y z r -> show (t, y, z, r)
    -- Term -> [a] -> Range
    , foldTupleTerm = \t l r -> show (t, l, r)
    -- Term -> a -> TypeQual -> Type -> Range
    , foldTypedTerm = \t z tq tp r -> show (t, z, tq, tp, r)
    -- Term -> VarDecl -> a -> Range
    , foldAsPattern = \t v z r -> show (t, v, z, r)
    -- Term -> Quantifier -> [GenVarDecl] -> a -> Range
    , foldQuantifiedTerm = \t q v z r -> show (t, q, v, z, r)
    -- Term -> [a] -> Partiality -> a -> Range
    , foldLambdaTerm = \t y p z r -> show (t, y, p, z, r)
    -- Term -> a -> [b] -> Range
    , foldCaseTerm = \t x b r -> show (t, x, b, r)
    -- Term -> LetBrand -> [b] -> a -> Range
    , foldLetTerm = \t l b z r -> show (t, l, b, z, r)
    -- Term -> Id -> [Type] -> [a] -> Range
    , foldResolvedMixTerm = \t i tp z r -> show (t, i, tp, z, r)
    -- Term -> Token
    , foldTermToken = \t tk -> show (t, tk)
    -- Term ->TypeQual -> Type -> Range
    , foldMixTypeTerm = \t tpq tp r -> show (t, tpq, tp, r)
    -- Term -> [a]
    , foldMixfixTerm = \t z -> show (t, z)
    -- Term -> BracketKind -> [a] -> Range
    , foldBracketTerm = \t k z r -> show (t, k, z, r)
    -- ProgEq -> a -> a -> Range
    , foldProgEq = \p y z r -> show (p, y, z, r)
    }



