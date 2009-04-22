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

simplify :: FORMULA -> FORMULA
simplify = foldFormula mapRecord
  { foldNegation = \ f n -> case f of
    True_atom p -> False_atom p
    False_atom p -> True_atom p
    Negation g _ -> g
    s -> Negation s n
  , foldConjunction = \ xs n -> case xs of
    [] -> True_atom n
    [x] -> x
    _ -> let
      ls = concatMap (\ f -> case f of
        Conjunction ys _ -> ys
        _ -> [f]) xs
      in if any is_False_atom ls then False_atom n else Conjunction ls n
  , foldDisjunction = \ xs n -> case xs of
    [] -> False_atom n
    [x] -> x
    _ -> let
      ls = concatMap (\ f -> case f of
        Disjunction ys _ -> ys
        _ -> [f]) xs
      in if any is_True_atom ls then True_atom n else Disjunction ls n
  , foldImplication = \ x y n -> case x of
    False_atom p -> True_atom p
    _ -> if is_True_atom x then y else Implication x y n
  , foldEquivalence = \ x y n ->
    if x == y then True_atom n else Equivalence x y n }


