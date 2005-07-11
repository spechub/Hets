{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module replaces Sorted_term(s) with explicit injection
   functions.  Don't do this after simplification since crucial sort
   information may be missing 
-}

module CASL.Inject where

import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.Fold
import Common.Id

-- | the name of injections
injName :: Id
injName = mkId [mkSimpleId "g__inj"]

inject :: [Pos] -> TERM f -> SORT -> TERM f
inject pos argument result_type = let argument_type = term_sort argument in
    if argument_type == result_type then argument else 
    Application (injOpSymb pos argument_type result_type) [argument] []

injOpSymb :: [Pos] -> SORT -> SORT -> OP_SYMB
injOpSymb pos s1 s2 =
    Qual_op_name injName (Op_type Total [s1] s2 pos) pos

injRecord :: (f -> f) -> Record f (FORMULA f) (TERM f)
injRecord mf = (mapRecord mf) 
     { foldApplication = \ _ o ts ps -> case o of
         Qual_op_name _ ty _ -> Application o 
             (zipWith (inject ps) ts $ args_OP_TYPE ty) ps
         _ -> error "injApplication"
     , foldSorted_term = \ _ st s ps -> inject ps st s
     , foldPredication = \ _ p ts ps -> case p of
         Qual_pred_name _ (Pred_type s _) _ -> Predication p
             (zipWith (inject ps) ts s) ps
         _ -> error "injPredication"
     }

injTerm :: (f -> f) -> TERM f -> TERM f
injTerm = foldTerm . injRecord

injFormula :: (f -> f) -> FORMULA f -> FORMULA f
injFormula = foldFormula . injRecord
