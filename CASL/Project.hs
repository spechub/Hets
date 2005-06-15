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

projTerm :: (f -> f) -> TERM f -> TERM f
projTerm mf t = case t of
   Application o@(Qual_op_name _ ty _) args ps -> 
       let newArgs = map (projTerm mf) args in
       Application o (zipWith (project ps) newArgs $ args_OP_TYPE ty) ps
   Sorted_term st s ps -> let
       newT = projTerm mf st
       in Sorted_term newT s ps
   Cast st s ps -> let
       newT = projTerm mf st
       in project ps newT s
   Conditional t1 f t2 ps -> let
       t3 = projTerm mf t1
       newF = projFormula mf f
       t4 = projTerm mf t2
       in Conditional t3 newF t4 ps 
   _ -> t

projFormula :: (f -> f) -> FORMULA f -> FORMULA f
projFormula mf f = case f of 
   Quantification q vs qf ps -> let
       newF = projFormula mf qf
       in Quantification q vs newF ps
   Conjunction fs ps -> let
       newFs = map (projFormula mf) fs
       in Conjunction newFs ps
   Disjunction fs ps -> let
       newFs = map (projFormula mf) fs
       in Disjunction newFs ps
   Implication f1 f2 b ps -> let
       f3 = projFormula mf f1
       f4 = projFormula mf f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = projFormula mf f1
       f4 = projFormula mf f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = projFormula mf nf
       in Negation newF ps
   Predication p@(Qual_pred_name _ (Pred_type s _) _) args ps -> 
       let newArgs = map (projTerm mf) args in
       Predication p (zipWith (project ps) newArgs s) ps
   Definedness t ps -> let 
       newT = projTerm mf t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = projTerm mf t1
       t4 = projTerm mf t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = projTerm mf t1
       t4 = projTerm mf t2
       in Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = projTerm mf t
       in Definedness (project ps newT s) ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   _ -> f 
