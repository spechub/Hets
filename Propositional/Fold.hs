{- |
Module      :  $Header$
Description :  folding function for propositional formulas
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

folding and simplification of propositional formulas

-}

module Propositional.Fold where

import Common.Id
import Propositional.AS_BASIC_Propositional

import qualified Data.Set as Set

data FoldRecord a = FoldRecord
  { foldNegation :: a -> Range -> a
  , foldConjunction :: [a] -> Range -> a
  , foldDisjunction :: [a] -> Range -> a
  , foldImplication :: a -> a -> Range -> a
  , foldEquivalence :: a -> a -> Range -> a
  , foldTrue_atom :: Range -> a
  , foldFalse_atom :: Range -> a
  , foldPredication :: Token -> a }

foldFormula :: FoldRecord a -> FORMULA -> a
foldFormula r frm = case frm of
   Negation f n -> foldNegation r (foldFormula r f) n
   Conjunction xs n -> foldConjunction r (map (foldFormula r) xs) n
   Disjunction xs n -> foldDisjunction r (map (foldFormula r) xs) n
   Implication x y n -> foldImplication r (foldFormula r x) (foldFormula r y) n
   Equivalence x y n -> foldEquivalence r (foldFormula r x) (foldFormula r y) n
   True_atom n -> foldTrue_atom r n
   False_atom n -> foldFalse_atom r n
   Predication x -> foldPredication r x

mapRecord :: FoldRecord FORMULA
mapRecord = FoldRecord
  { foldNegation = Negation
  , foldConjunction = Conjunction
  , foldDisjunction = Disjunction
  , foldImplication = Implication
  , foldEquivalence = Equivalence
  , foldTrue_atom = True_atom
  , foldFalse_atom = False_atom
  , foldPredication = Predication }

isNeg :: FORMULA -> Bool
isNeg f = case f of
  Negation _ _ -> True
  _ -> False

getLits :: Set.Set FORMULA -> Set.Set FORMULA
getLits = Set.fold (\ f -> case f of
  Negation x _ -> Set.insert x
  _ -> Set.insert f) Set.empty

bothLits :: Set.Set FORMULA -> Bool
bothLits fs = let
  (ns, ps) = Set.partition isNeg fs
  in not $ Set.null $ Set.intersection (getLits ns) (getLits ps)

flatConj :: [FORMULA] -> Set.Set FORMULA
flatConj = Set.fromList
  . concatMap (\ f -> case f of
      True_atom _ -> []
      Conjunction fs _ -> fs
      _ -> [f])

mkConj :: [FORMULA] -> Range -> FORMULA
mkConj fs n = let s = flatConj fs in
  if Set.member (False_atom nullRange) s || bothLits s then False_atom n else
  case Set.toList s of
    [] -> True_atom n
    [x] -> x
    ls -> Conjunction ls n

flatDisj :: [FORMULA] -> Set.Set FORMULA
flatDisj = Set.fromList
  . concatMap (\ f -> case f of
      False_atom _ -> []
      Disjunction fs _ -> fs
      _ -> [f])

mkDisj :: [FORMULA] -> Range -> FORMULA
mkDisj fs n = let s = flatDisj fs in
  if Set.member (True_atom nullRange) s || bothLits s then True_atom n else
  case Set.toList s of
    [] -> False_atom n
    [x] -> x
    ls -> Disjunction ls n

simplify :: FORMULA -> FORMULA
simplify = foldFormula mapRecord
  { foldNegation = \ f n -> case f of
    True_atom p -> False_atom p
    False_atom p -> True_atom p
    Negation g _ -> g
    s -> Negation s n
  , foldConjunction = mkConj
  , foldDisjunction = mkDisj
  , foldImplication = \ x y n -> case x of
    False_atom p -> True_atom p
    _ -> if x == y then True_atom n else case x of
           True_atom _ -> y
           False_atom _ -> True_atom n
           Negation z _ | z == y -> x
           _ -> case y of
             Negation z _ | z == x -> x
             _ -> Implication x y n
  , foldEquivalence = \ x y n -> case compare x y of
    LT -> case y of
      Negation z _ | x == z -> False_atom n
      _ -> Equivalence x y n
    EQ -> True_atom n
    GT -> case x of
      Negation z _ | z == y -> False_atom n
      _ -> Equivalence y x n }

elimEquiv :: FORMULA -> FORMULA
elimEquiv = foldFormula mapRecord
  { foldEquivalence = \ x y n ->
    Conjunction [Implication x y n, Implication y x n] n }

elimImpl :: FORMULA -> FORMULA
elimImpl = foldFormula mapRecord
  { foldImplication = \ x y n ->
    Disjunction [Negation x n, y] n }
