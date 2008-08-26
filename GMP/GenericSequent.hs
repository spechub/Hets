{-# OPTIONS -fglasgow-exts #-}
module GenericSequent where

import AbstractSyntax
import Data.List

-- | Generate all possible clauses out of a list of atoms
allClauses :: [a] -> [Clause a]
allClauses x = case x of
                 h:t -> let addPositive c (Implies n p) = Implies n (c:p)
                            addNegative c (Implies n p) = Implies (c:n) p
                        in map (addPositive h) (allClauses t) ++
                           map (addNegative h) (allClauses t)
                 _   -> [Implies [] []]

-- | Extract the modal atoms from a formula 
getMA :: Eq a => Boole a -> [Boole a]
getMA x = case x of
            And phi psi -> (getMA phi) `union` (getMA psi)
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

-- | DNF: disjunctive normal form
dnf :: (Eq a) => Boole a -> [Clause (Boole a)]
dnf phi = filter (\x -> eval (subst phi x)) (allClauses (getMA phi))

-- | CNF: conjunctive normal form
cnf :: (Eq a) => Boole a -> [Clause (Boole a)]
cnf phi = map (\(Implies x y) -> Implies y x) (dnf (Not phi))

-- | Provability function
--provable :: Logic a b => Boole (a c) -> Bool
--provable phi = all (\c -> any (all provable) (map fst (match c))) (cnf phi)


unwrapK = \(K x) -> x
unwrapKD = \(KD x) -> x
