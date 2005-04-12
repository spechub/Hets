{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  resolve empty conjunctions and other trivial cases
-}

module CASL.Simplify where

import CASL.AS_Basic_CASL

simplifyTerm :: Eq f => (f -> f) -> TERM f -> TERM f
simplifyTerm mf t = case t of
   Application o args ps -> 
       Application o (map (simplifyTerm mf) args) ps
   Sorted_term st s ps -> Sorted_term (simplifyTerm mf st) s ps
   Cast st s ps -> Cast (simplifyTerm mf st) s ps
   Conditional t1 f t2 ps -> let
       t3 = simplifyTerm mf t1
       newF = simplifyFormula mf f
       t4 = simplifyTerm mf t2
       in case newF of 
          True_atom _ -> t3 
          False_atom _ -> t4 
          _ -> Conditional t3 newF t4 ps 
   _ -> t

simplifyFormula :: Eq f => (f -> f) -> FORMULA f -> FORMULA f
simplifyFormula mf form = case form of 
   Quantification q vs qf ps -> let
       newF = simplifyFormula mf qf
       in if null vs then newF else
          case newF of 
          True_atom _ -> newF 
          False_atom _ -> newF 
          _ -> Quantification q vs newF ps
   Conjunction fs ps -> case fs of 
       [] -> True_atom ps
       [f] -> f 
       _ -> Conjunction (map (simplifyFormula mf) fs) ps
   Disjunction fs ps -> 
       case fs of 
       [] -> False_atom ps
       [f] -> f 
       _ -> Disjunction (map (simplifyFormula mf) fs) ps
   Implication f1 f2 b ps -> let
       f3 = simplifyFormula mf f1
       f4 = simplifyFormula mf f2
       in case f3 of 
       True_atom _ -> f4
       _ -> Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = simplifyFormula mf f1
       f4 = simplifyFormula mf f2
       in case f4 of 
       True_atom _ -> f3 
       _ -> case f3 of 
            True_atom _ -> f4
            _ -> if f3 == f4 then True_atom ps else Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = simplifyFormula mf nf
       in case newF of
          False_atom qs -> True_atom (qs ++ ps)
          True_atom qs -> False_atom (qs ++ ps)
          _ -> Negation newF ps
   Predication p args ps -> 
       let newArgs = map (simplifyTerm mf) args in
       Predication p newArgs ps
   Definedness t ps -> let 
       newT = simplifyTerm mf t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = simplifyTerm mf t1
       t4 = simplifyTerm mf t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = simplifyTerm mf t1
       t4 = simplifyTerm mf t2
       in if t3 == t4 then True_atom ps else Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = simplifyTerm mf t
       in Membership newT s ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   _ -> form 
