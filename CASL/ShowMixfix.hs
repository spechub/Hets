{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module puts parenthesis around mixfix terms for 
   unambiguous pretty printing
-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL
import qualified CASL.Fold as Fold

mkMixfixRecord :: (f -> f) -> Fold.Record f (FORMULA f) (TERM f)
mkMixfixRecord mf = Fold.idRecord 
     { Fold.foldApplication = \ _ o ts ps ->
         if null ts then Application o ts ps else 
         Mixfix_term [Application o [] [], Mixfix_parenthesized ts ps]
     , Fold.foldPredication = \ _ p ts ps -> 
         if null ts then Predication p ts ps else Mixfix_formula $ 
            Mixfix_term [Mixfix_qual_pred p, Mixfix_parenthesized ts ps]
     , Fold.foldExtFORMULA = \ _ f -> ExtFORMULA $ mf f
     }

mapTerm :: (f -> f) -> TERM f -> TERM f
mapTerm = Fold.mapTerm . mkMixfixRecord

mapFormula :: (f -> f) -> FORMULA f -> FORMULA f
mapFormula = Fold.mapFormula . mkMixfixRecord
