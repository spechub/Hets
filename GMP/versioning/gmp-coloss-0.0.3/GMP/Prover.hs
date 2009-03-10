{- | Module     : $Header$
 -  Description : Implementation of the generic sequent calculus
 -  Copyright   : (c) Daniel Hausmann & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions for several logics.
 - Currently implemented: K, KD, Mon, HM, C, P, G
 -}

module GMP.Prover where
import List
import Ratio
import Maybe

import Debug.Trace

import GMP.Generic

--------------------------------------------------------------------------------
-- basic sequent function(s)
--------------------------------------------------------------------------------

-- expand applies all sequent rules that do not induce branching
expand :: (Logic a) => Sequent a -> Sequent a
expand s | seq s $ False = undefined -- force strictness
expand [] = []
expand ((Neg (Neg phi)):as) = expand (phi:as)
expand ((Neg (And phi psi)):as) = expand ((Neg phi):(Neg psi):as)
expand (a:as) = a:(expand as)

--------------------------------------------------------------------------------
-- sequent calculus implementation
--------------------------------------------------------------------------------

--Inference Rules
-- map a sequent to the list of all premises that derive
-- the sequent. Note that a premise is a list of sequents:
-- * to prove Gamma, A /\ B we need both Gamma, A and Gamma, B as premises.
-- * to prove Gamma, neg(A /\ B), we need Gamma, neg A, neg B as premise.
-- * to prove A, neg A, Gamma we need no premises
-- So a premise is a list of sequents, and the list of all possible
-- premises therefore has type [[ Sequent ]]

-- the functions below compute the list of all possible premises
-- that allow to derive a given sequent using the rule that
-- lends its name to the function.

-- faster to check for atomic axioms
-- axiom1 xs = [ []  | p <- xs, (Not q) <- xs, p==q]
axiom_rule  :: (Logic a) => Sequent a -> [[Sequent a]]
axiom_rule xs = nub [ []  | (Atom n) <- xs, (Neg (Atom m)) <- xs, m==n]

true_rule :: (Logic a) => Sequent a -> [[Sequent a]]
true_rule xs = nub [ []  | T <- xs]

negfalse_rule :: (Logic a) => Sequent a -> [[Sequent a]]
negfalse_rule xs = nub [ []  | (Neg F) <- xs]

-- two variants here: use @-patterns or ``plain'' recursion.
conj_rule :: (Logic a) => Sequent a -> [[ Sequent a]]
conj_rule s | seq s $ False = undefined -- force strictness
conj_rule as = [ [ (p: delete f as) , ( q: delete f as )] | f@(And p q ) <- as]

-- the rule for the modal operator
modal_rule :: (Logic a) => Sequent a -> [[Sequent a]]
modal_rule xs = match xs

-- collect all possible premises, i.e. the union of the possible
-- premises taken over the set of all rules in one to  get the
-- recursion off the ground.

-- CAVEAT: the order of axioms /rules has a HUGE impact on performance.
-- this is as good as it gets if we apply the individual rules
-- message for the afterworld: if youm want to find proofs quickly,
-- first look at the rules that induce branching.
-- we can do slightly better if we apply all rules that do not
-- induce branching in one single step.
allRules :: (Logic a) => Sequent a -> [[Sequent a]]
allRules s = let t = expand s in trace ("\n  Axiom-rule: " ++ show(map (map (map pretty)) (axiom_rule $ t) ) ++
                                        "  True-rule: " ++ show(map (map (map pretty)) (true_rule $ t) ) ++
                                        "  NegFalse-rule: " ++ show(map (map (map pretty)) (negfalse_rule $ t) ) ++
                                        "  Modal-rule: " ++ show(map (map (map pretty)) (modal_rule $ t) ) ++
                                        "  Conj-rule: " ++ show(map (map (map pretty)) (conj_rule $ t) ) ) $ 
                                 (axiom_rule $ t) ++ (true_rule $ t) ++ (negfalse_rule $ t) ++ (conj_rule $ t) ++ (modal_rule $ t)

-- A sequent is provable iff there exists a set of premises that
-- prove the sequent such that all elements in the list of premises are
-- themselves provable.
sprovable :: (Logic a) => Sequent a -> Bool
sprovable s | seq s $ False = undefined -- force strictness
sprovable s = trace ("\n  Sequent:" ++ show( map pretty (expand s) )) $ 
                      any  (\p -> (all sprovable p)) (allRules s)

-- specialisation to formulas
sequent_provable :: (Logic a) => L a -> Bool
sequent_provable phi = sprovable [ phi ]

-- a formula is satisfiable iff it's negation is not provable
sequent_satisfiable :: (Logic a) => L a -> Bool
sequent_satisfiable phi = not $ sequent_provable $ (Neg phi)

