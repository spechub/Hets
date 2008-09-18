{- |
Module      :  $Header$
Description :  resolve empty conjunctions and other trivial cases
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Resolve empty conjunctions and other trivial cases
-}

module CASL.Simplify where

import CASL.AS_Basic_CASL
import CASL.Fold
import Data.List(nub)

simplifyRecord :: Eq f => (f -> f) -> Record f (FORMULA f) (TERM f)
simplifyRecord mf = (mapRecord mf)
    { foldConditional = \ _ t1 f t2 ps -> case f of
      True_atom _ -> t1
      False_atom _ -> t2
      _ -> Conditional t1 f t2 ps
    , foldQuantification = \ _ q vs qf ps ->
      let nf = Quantification q vs qf ps in
      case q of
      Unique_existential -> nf
      _ -> if null vs then qf else case (qf, q) of
           (True_atom _, Universal) -> qf
           (False_atom _, Existential) -> qf
           _ -> nf
    , foldConjunction = \ _ fs ps -> if any is_False_atom fs
      then False_atom ps else case nub $ filter (not . is_True_atom) fs of
      [] -> True_atom ps
      [f] -> f
      rs -> Conjunction rs ps
    , foldDisjunction = \ _ fs ps -> if any is_True_atom fs
      then True_atom ps else case nub $ filter (not . is_False_atom) fs of
      [] -> False_atom ps
      [f] -> f
      rs -> Disjunction rs ps
    , foldImplication = \ _ f1 f2 b ps -> case f1 of
      True_atom _ -> f2
      False_atom _ -> True_atom ps
      _ -> case f2 of
           True_atom _ -> f2
           _ -> if f1 == f2 then True_atom ps else Implication f1 f2 b ps
    , foldEquivalence = \ _ f1 f2 ps -> case f2 of
      True_atom _ -> f1
      False_atom _ -> case f1 of
           True_atom _ -> False_atom ps
           False_atom _ -> True_atom ps
           _ -> Negation f1 ps
      _ -> case f1 of
           True_atom _ -> f2
           False_atom _ -> Negation f2 ps
           _ -> if f1 == f2 then True_atom ps else Equivalence f1 f2 ps
    , foldNegation = \ _ nf ps -> case nf of
      False_atom _ -> True_atom ps
      True_atom _ -> False_atom ps
      _ -> Negation nf ps
    , foldStrong_equation = \ _ t1 t2 ps ->
      if t1 == t2 then True_atom ps else Strong_equation t1 t2 ps
    }

simplifyTerm :: Eq f => (f -> f) -> TERM f -> TERM f
simplifyTerm = foldTerm . simplifyRecord

simplifyFormula :: Eq f => (f -> f) -> FORMULA f -> FORMULA f
simplifyFormula = foldFormula . simplifyRecord
