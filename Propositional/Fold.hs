{- |
Module      :  $Header$
Description :  folding function for propositional formulas
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher

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

getConj :: FORMULA -> [FORMULA]
getConj f = case f of
  Conjunction xs _ -> xs
  True_atom _ -> []
  _ -> [f]

getDisj :: FORMULA -> [FORMULA]
getDisj f = case f of
  Disjunction xs _ -> xs
  False_atom _ -> []
  _ -> [f]

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
    ls -> Conjunction (map (flip mkDisj n . Set.toList)
      $ foldr ((\ l ll ->
        if any (`Set.isSubsetOf` l) ll then ll else
          l : filter (not . Set.isSubsetOf l) ll)
          . Set.fromList . getDisj) [] ls) n

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
    ls -> Disjunction (map (flip mkConj n . Set.toList)
      $ foldr ((\ l ll ->
        if any (`Set.isSubsetOf` l) ll then ll else
          l : filter (not . Set.isSubsetOf l) ll)
          . Set.fromList . getConj) [] ls) n

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

negForm :: Range -> FORMULA -> FORMULA
negForm r frm = case frm of
  Negation f _ -> case f of
    Negation nf _ -> negForm r nf
    _ -> f
  Conjunction xs n -> Disjunction (map (negForm r) xs) n
  Disjunction xs n -> Conjunction (map (negForm r) xs) n
  True_atom n -> False_atom n
  False_atom n -> True_atom n
  _ -> Negation frm r

moveNegIn :: FORMULA -> FORMULA
moveNegIn frm = case frm of
  Negation f n -> negForm n f
  Conjunction xs n -> Conjunction (map moveNegIn xs) n
  Disjunction xs n -> Disjunction (map moveNegIn xs) n
  _ -> frm

distributeAndOverOr :: FORMULA -> FORMULA
distributeAndOverOr f = case f of
  Conjunction xs n -> mkConj (map distributeAndOverOr xs) n
  Disjunction xs n -> if all isPrimForm xs then mkDisj xs n else
    distributeAndOverOr
    $ mkConj (map (`mkDisj` n) . combine $ map getConj xs) n
  _ -> f

cnf :: FORMULA -> FORMULA
cnf = flipLiterals . distributeAndOverOr . moveNegIn . elimImpl . elimEquiv

flipLiterals :: FORMULA -> FORMULA
flipLiterals f = case f of
  Negation p@(Predication _) _ -> p
  Predication t -> Negation f $ tokPos t
  Conjunction xs n -> Conjunction (map flipLiterals xs) n
  Disjunction xs n -> Disjunction (map flipLiterals xs) n
  _ -> f

distributeOrOverAnd :: FORMULA -> FORMULA
distributeOrOverAnd f = case f of
  Disjunction xs n -> mkDisj (map distributeOrOverAnd xs) n
  Conjunction xs n -> if all isPrimForm xs then mkConj xs n else
    distributeOrOverAnd
    $ mkDisj (map (`mkConj` n) . combine $ map getDisj xs) n
  _ -> f

dnf :: FORMULA -> FORMULA
dnf = distributeOrOverAnd . moveNegIn . elimImpl . elimEquiv

combine :: [[a]] -> [[a]]
combine l = case l of
  [] -> [[]]
  h : t -> concatMap (flip map h . flip (:)) (combine t)
