{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{-# OPTIONS -fglasgow-exts #-}
module GenericSequent where

import ModalLogic
import CombLogic
import Data.List as List
--import Data.Map as Map

-- | Generate all possible clauses out of a list of atoms
allClauses :: [a] -> [Clause a]
allClauses x = case x of
                 h:t -> let addPositive c (Implies n p) = Implies n (c:p)
                            addNegative c (Implies n p) = Implies (c:n) p
                        in List.map (addPositive h) (allClauses t) ++
                           List.map (addNegative h) (allClauses t)
                 _   -> [Implies [] []]

-- | Extract the modal atoms from a formula
getMA :: Eq a => Boole a -> [Boole a]
getMA x = case x of
            And phi psi -> (getMA phi) `List.union` (getMA psi)
            Not phi     -> getMA phi
            At phi      -> [At phi]
            _           -> []

-- | Substitution of modal atoms within a "Boole" expression
subst :: Eq a => Boole a -> Clause (Boole a) -> Boole a
subst x s@(Implies neg pos) =
  case x of
    And phi psi -> And (subst phi s) (subst psi s)
    Not phi     -> Not (subst phi s)
    T           -> T
    F           -> F
    _           -> if (elem x neg) then F
                   else if (elem x pos) then T
                   else error "GenericSequent.subst"

-- | Evaluation of an instantiated "Boole" expression
eval :: Boole a -> Bool
eval x = case x of
           And phi psi -> (eval phi) && (eval psi)
           Not phi     -> not (eval phi)
           T           -> True
           F           -> False
           _           -> error "GenericSequent.eval"

-- | DNF: disjunctive normal form of a Boole expression
dnf :: (Eq a) => Boole a -> [Clause (Boole a)]
dnf phi = List.filter (\x -> eval (subst phi x)) (allClauses (getMA phi))

-- | CNF: conjunctive normal form of a Boole expression
cnf :: (Eq a) => Boole a -> [Clause (Boole a)]
cnf phi = List.map (\(Implies x y) -> Implies y x) (dnf (Not phi))

-- | Generic Provability Function
provable :: (Eq a, Form a b c) => Boole a -> Bool
provable _ = True
{-
provable phi =
  let unwrap (Subst x) = Map.elems x
  in all (\c -> any (all provable) (List.map unwrap.snd (match c))) (cnf phi)
-}

-- | Generic Satisfiability Function
sat :: (Eq a, Form a b c) => Boole a -> Bool
sat phi = not $ provable $ neg phi

-- | Function for "normalizing" negation
neg :: Eq a => Boole a -> Boole a
neg phi = case phi of
            Not psi -> psi
            _       -> phi

