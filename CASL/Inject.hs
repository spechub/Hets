{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   This module replaces Sorted_term(s) with explicit injection
   functions.  Don't do this after simplification since crucial sort
   information may be missing 
-}

module CASL.Inject where

import CASL.AS_Basic_CASL
import CASL.Overload
import Common.Id

-- | the name of injections
injName :: Id
injName = mkId [mkSimpleId "inj"]

inject :: [Pos] -> TERM f -> SORT -> TERM f
inject pos argument result_type = let argument_type = term_sort argument in
    if argument_type == result_type then argument else 
    Application (injOpSymb pos argument_type result_type) [argument] []

injOpSymb :: [Pos] -> SORT -> SORT -> OP_SYMB
injOpSymb pos s1 s2 =
    Qual_op_name injName (Op_type Total [s1] s2 pos) pos

injTerm :: (f -> f) -> TERM f -> TERM f
injTerm mf t = case t of
   Application o@(Qual_op_name _ ty _) args ps -> 
       let newArgs = map (injTerm mf) args in
       Application o (zipWith (inject ps) newArgs $ args_OP_TYPE ty) ps
   Sorted_term st s ps -> let 
       newT = injTerm mf st 
       in inject ps newT s
   Cast st s ps -> let
       newT = injTerm mf st
       in Cast newT s ps
   Conditional t1 f t2 ps -> let
       t3 = injTerm mf t1
       newF = injFormula mf f
       t4 = injTerm mf t2
       in Conditional t3 newF t4 ps 
   _ -> t

injFormula :: (f -> f) -> FORMULA f -> FORMULA f
injFormula mf f = case f of 
   Quantification q vs qf ps -> let
       newF = injFormula mf qf
       in Quantification q vs newF ps
   Conjunction fs ps -> let
       newFs = map (injFormula mf) fs
       in Conjunction newFs ps
   Disjunction fs ps -> let
       newFs = map (injFormula mf) fs
       in Disjunction newFs ps
   Implication f1 f2 b ps -> let
       f3 = injFormula mf f1
       f4 = injFormula mf f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = injFormula mf f1
       f4 = injFormula mf f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = injFormula mf nf
       in Negation newF ps
   Predication p@(Qual_pred_name _ (Pred_type s _) _) args ps -> 
       let newArgs = map (injTerm mf) args in
       Predication p (zipWith (inject ps) newArgs s) ps
   Definedness t ps -> let 
       newT = injTerm mf t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = injTerm mf t1
       t4 = injTerm mf t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = injTerm mf t1
       t4 = injTerm mf t2
       in Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = injTerm mf t
       in Membership newT s ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   _ -> f 
