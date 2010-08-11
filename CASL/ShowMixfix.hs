{- |
Module      :  $Header$
Description :  uniquely show mixfix terms with sufficient parenthesis
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Put parenthesis around mixfix terms, for unambiguous pretty printing
-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL
import CASL.Fold
import Common.Id

mkMixfixRecord :: (f -> f) -> Record f (FORMULA f) (TERM f)
mkMixfixRecord mf = (mapRecord mf)
     { foldApplication = \ _ o ts ps ->
         if null ts then Application o ts ps else
         Mixfix_term [Application o [] nullRange, Mixfix_parenthesized ts ps]
     , foldPredication = \ _ p ts ps ->
         if null ts then Predication p ts ps else Mixfix_formula $
            Mixfix_term [Mixfix_qual_pred p, Mixfix_parenthesized ts ps]
     }

mapTerm :: (f -> f) -> TERM f -> TERM f
mapTerm = foldTerm . mkMixfixRecord

mapFormula :: (f -> f) -> FORMULA f -> FORMULA f
mapFormula = foldFormula . mkMixfixRecord
