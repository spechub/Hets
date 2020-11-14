{- |
Module      :  ./CASL/Simplify.hs
Description :  resolve empty conjunctions and other trivial cases
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Resolve empty conjunctions and other trivial cases
-}

module CASL.Simplify where

import CASL.AS_Basic_CASL
import CASL.Fold

import Common.Id
import Common.Utils (nubOrd)

import Data.Hashable

negateFormula :: FORMULA f -> Maybe (FORMULA f)
negateFormula f = case f of
  Sort_gen_ax {} -> Nothing
  _ -> Just $ negateForm f nullRange

mkJunction :: (Ord f, Hashable f) => Junctor -> [FORMULA f] -> Range -> FORMULA f
mkJunction j fs ps = let
    (isTop, top, join) = case j of
        Con -> (is_False_atom, False, conjunctRange)
        Dis -> (is_True_atom, True, disjunctRange)
    in case nubOrd $ concatMap (\ f -> case f of
           Junction j2 ffs _ | j == j2 -> ffs
           Negation (Junction j2 ffs _) p | j /= j2 ->
             map (`negateForm` p) ffs
           Atom b _ | b /= top -> []
           _ -> [f]) fs of
         flat -> if any (\ f -> isTop f || elem (mkNeg f) flat) flat
           then Atom top ps else join flat ps

mkRelation :: Ord f => FORMULA f -> Relation -> FORMULA f -> Range -> FORMULA f
mkRelation f1 c f2 ps =
    let nf1 = negateForm f1 ps
        tf = Atom True ps
        equiv = c == Equivalence
    in case f1 of
      Atom b _
        | b -> f2
        | equiv -> negateForm f2 ps
        | otherwise -> tf
      _ -> case f2 of
           Atom b _
             | not b -> nf1
             | equiv -> f1
             | otherwise -> tf
           _ | f1 == f2 -> tf
             | nf1 == f2 -> if equiv then Atom False ps else f1
           _ -> Relation f1 c f2 ps

mkEquation :: Ord f => TERM f -> Equality -> TERM f -> Range -> FORMULA f
mkEquation t1 e t2 ps =
  if e == Strong && t1 == t2 then Atom True ps else Equation t1 e t2 ps

simplifyRecord :: (Ord f, Hashable f) => (f -> f) -> Record f (FORMULA f) (TERM f)
simplifyRecord mf = (mapRecord mf)
    { foldConditional = \ _ t1 f t2 ps -> case f of
      Atom b _ -> if b then t1 else t2
      _ -> Conditional t1 f t2 ps
    , foldQuantification = \ _ q vs qf ps ->
      let nf = Quantification q vs qf ps in
      case q of
      Unique_existential -> nf
      _ -> if null vs then qf else case (qf, q) of
           (Atom True _, Universal) -> qf
           (Atom False _, Existential) -> qf
           _ -> nf
    , foldJunction = const mkJunction
    , foldRelation = const mkRelation
    , foldNegation = const negateForm
    , foldEquation = const mkEquation
    }

simplifyTerm :: (Ord f, Hashable f) => (f -> f) -> TERM f -> TERM f
simplifyTerm = foldTerm . simplifyRecord

simplifyFormula :: (Ord f, Hashable f) => (f -> f) -> FORMULA f -> FORMULA f
simplifyFormula = foldFormula . simplifyRecord
