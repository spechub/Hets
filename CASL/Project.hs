{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module replaces Cast(s) with explicit projection
   functions.  Don't do this after simplification since crucial sort
   information may be missing 

   Membership test are replaced with Definedness formulas
-}

module CASL.Project where

import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.Fold
import Common.Id

-- | the name of projections
projName :: Id
projName = mkId [mkSimpleId "g__proj"]

project :: [Pos] -> TERM f -> SORT -> TERM f
project pos argument result_type = let argument_type = term_sort argument in
    if argument_type == result_type then argument else 
    Application (projOpSymb pos argument_type result_type) [argument] []

projOpSymb :: [Pos] -> SORT -> SORT -> OP_SYMB
projOpSymb pos s1 s2 =
    Qual_op_name projName (Op_type Total [s1] s2 pos) pos

projRecord :: (f -> f) -> Record f (FORMULA f) (TERM f)
projRecord mf = (mapRecord mf) 
     { foldApplication = \ _ o ts ps -> case o of
         Qual_op_name _ ty _ -> Application o 
             (zipWith (project ps) ts $ args_OP_TYPE ty) ps
         _ -> error "profApplication"
     , foldCast = \ _ st s ps -> project ps st s
     , foldPredication = \ _ p ts ps -> case p of
         Qual_pred_name _ (Pred_type s _) _ -> Predication p
             (zipWith (project ps) ts s) ps
         _ -> error "projPredication"
     , foldMembership = \ _ t s ps -> Definedness (project ps t s) ps
     }

projTerm :: (f -> f) -> TERM f -> TERM f
projTerm = foldTerm . projRecord

projFormula :: (f -> f) -> FORMULA f -> FORMULA f
projFormula = foldFormula . projRecord
