{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   This module puts parenthesis around mixfix term for 
   unambiguous pretty printing
-}

module CASL.ShowMixfix where

import CASL.AS_Basic_CASL

mapTerm :: (f -> f) -> TERM f -> TERM f
mapTerm mf t = case t of
   Application o ts@(_:_) ps -> 
       Mixfix_term [Application o [] [], Mixfix_parenthesized 
                                (map (mapTerm mf) ts) ps]
   Sorted_term st s ps -> let
       newT = mapTerm mf st
       in Sorted_term newT s ps
   Cast st s ps -> let
       newT = mapTerm mf st
       in Cast newT s ps
   Conditional t1 f t2 ps -> let
       t3 = mapTerm mf t1
       newF = mapFormula mf f
       t4 = mapTerm mf t2
       in Conditional t3 newF t4 ps 
   Mixfix_term ts -> let 
       newTs = map (mapTerm mf) ts
       in Mixfix_term newTs
   Mixfix_parenthesized ts ps -> let 
       newTs = map (mapTerm mf) ts
       in Mixfix_parenthesized newTs ps
   Mixfix_bracketed ts ps -> let 
       newTs = map (mapTerm mf) ts
       in Mixfix_bracketed newTs ps
   Mixfix_braced ts ps -> let 
       newTs = map (mapTerm mf) ts
       in Mixfix_braced newTs ps
   _ -> t

mapFormula :: (f -> f) -> FORMULA f -> FORMULA f
mapFormula mf f = case f of 
   Quantification q vs qf ps -> let
       newF = mapFormula mf qf
       in Quantification q vs newF ps
   Conjunction fs ps -> let
       newFs = map (mapFormula mf) fs
       in Conjunction newFs ps
   Disjunction fs ps -> let
       newFs = map (mapFormula mf) fs
       in Disjunction newFs ps
   Implication f1 f2 b ps -> let
       f3 = mapFormula mf f1
       f4 = mapFormula mf f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = mapFormula mf f1
       f4 = mapFormula mf f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = mapFormula mf nf
       in Negation newF ps
   Predication p ts@(_:_) ps -> 
       Mixfix_formula $ Mixfix_term [Mixfix_qual_pred p, Mixfix_parenthesized 
                                (map (mapTerm mf) ts) ps]
   Definedness t ps -> let 
       newT = mapTerm mf t
       in Definedness newT ps
   Existl_equation t1 t2 ps -> let
       t3 = mapTerm mf t1
       t4 = mapTerm mf t2
       in Existl_equation t3 t4 ps
   Strong_equation t1 t2 ps -> let
       t3 = mapTerm mf t1
       t4 = mapTerm mf t2
       in Strong_equation t3 t4 ps
   Membership t s ps -> let 
       newT = mapTerm mf t
       in Membership newT s ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   Mixfix_formula t -> Mixfix_formula $ mapTerm mf t
   _ -> f 
