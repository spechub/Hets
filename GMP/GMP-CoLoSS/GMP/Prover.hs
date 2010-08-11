{- | Module     : $Header$
 -  Description : Implementation of the generic sequent calculus
 -  Copyright   : (c) Daniel Hausmann & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the generic proving function.
 - Also contains an optimized version of the proving function (using so-called
 - 'memoizing')
 -}

module GMP.Prover where
import List
import Ratio
import Maybe

import Debug.Trace

import GMP.Logics.Generic
import GMP.Logics.K

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
axiom_rule :: Sequent -> Premises
axiom_rule (Sequent xs) = [ [[Sequent ([]::[Formula (K (K (K ())))])]]  | (Atom n) <- xs, (Neg (Atom m)) <- xs, m==n]

true_rule :: Sequent -> Premises
true_rule (Sequent xs) = [ [[Sequent ([]::[Formula (K (K (K ())))])]]  | T <- xs]

negfalse_rule :: Sequent -> Premises
negfalse_rule (Sequent xs) = [ [[Sequent ([]::[Formula (K (K (K ())))])]]  | (Neg F) <- xs]

conj_rule :: Sequent -> Premises
conj_rule (Sequent as) = [ [[(Sequent (p: delete f as))],[(Sequent (q: delete f as))]] | f@(And p q) <- as]

-- the rule for the modal operator
modal_rule :: [Bool] -> Sequent -> Premises
modal_rule flags (Sequent xs) = emptify (fMatch flags xs)

-- the rule for the modal operator - optimised version
omodal_rule :: [Bool] -> [Sequent] -> Sequent -> Premises
omodal_rule flags [Sequent ec] (Sequent xs) = emptify (fMatchOptimised flags xs [])

-- collect all possible premises, i.e. the union of the possible
-- premises taken over the set of all rules in one to  get the
-- recursion off the ground.

-- CAVEAT: the order of axioms /rules has a HUGE impact on performance.
-- this is as good as it gets if we apply the individual rules
-- message for the afterworld: if youm want to find proofs quickly,
-- first look at the rules that induce branching.
-- we can do slightly better if we apply all rules that do not
-- induce branching in one single step.
allRules :: [Bool] -> Sequent -> Premises
allRules flags (Sequent seq) = let t = Sequent (expand seq)
                                   axioms = axiom_rule $ t
                                   trues = true_rule $ t
                                   negfalses = negfalse_rule $ t
                                   modals = modal_rule flags t
                                   conjs = conj_rule $ t
                               in if (flags!!1) then
                                         trace ("\n  Axiom-rule: "    ++ (prettylll axioms) ++
                                                "  True-rule: "     ++ (prettylll trues) ++
                                                "  NegFalse-rule: " ++ (prettylll negfalses) ++
                                                "  Modal-rule: "    ++ (prettylll modals) ++
                                                "  Conj-rule: "     ++ (prettylll conjs) ) $ 
                                        (axioms ++ trues ++ negfalses ++ conjs ++ modals)
                                                else
                                        (axioms ++ trues ++ negfalses ++ conjs ++ modals)

oallRules :: [Bool] -> [Sequent] -> Sequent -> Premises
oallRules flags ec (Sequent seq) = let t = Sequent (expand seq)
                                       axioms = axiom_rule $ t
                                       trues = true_rule $ t
                                       negfalses = negfalse_rule $ t
                                       modals = omodal_rule flags ec t
                                       conjs = conj_rule $ t
                                   in trace ("\n  Axiom-rule: "    ++ (prettylll axioms) ++
                                             "  True-rule: "     ++ (prettylll trues) ++
                                             "  NegFalse-rule: " ++ (prettylll negfalses) ++
                                             "  Modal-rule: "    ++ (prettylll modals) ++
                                             "  Conj-rule: "     ++ (prettylll conjs) ) $ 
                                     (axioms ++ trues ++ negfalses ++ conjs ++ modals)

-- A sequent is provable iff there exists a set of premises that
-- prove the sequent such that all elements in the list of premises are
-- themselves provable.
sprovable :: [Bool] -> Sequent -> Bool
sprovable flags (Sequent []) = True
sprovable flags (Sequent seq) = if (flags!!1) then trace ("\n  <Current Sequent:> " ++ (pretty_seq (Sequent (expand seq)))) $
                                                   any (\p -> (all (\q -> any (sprovable flags) q) p)) (allRules flags (Sequent seq))
                                              else any (\p -> (all (\q -> any (sprovable flags) q) p)) (allRules flags (Sequent seq))

-- optimized, alla
osprovable :: [Bool] -> [Sequent] -> Sequent -> Bool
osprovable flags ec (Sequent []) = True
osprovable flags ec (Sequent seq) = trace ("\n  <Current Sequent:> " ++ (pretty_seq (Sequent (expand seq)))) $
                                    any (\p -> (all (\q -> any (osprovable flags ec) q) p)) (oallRules flags ec (Sequent seq))

-- specialisation to formulae
provable :: (SigFeature a b (c d), Eq (a (b (c d)))) => Formula (a (b (c d))) -> [Bool] -> Bool
provable phi flags = sprovable flags (Sequent [phi])

oprovable :: (SigFeature a b (c d), Eq (a (b (c d)))) => [Bool] -> [Sequent] -> Formula (a (b (c d))) -> Bool
oprovable flags ec phi = osprovable flags ec (Sequent [phi])

-- a formula is satisfiable iff it's negation is not provable
satisfiable :: (SigFeature a b (c d), Eq (a (b (c d)))) => Formula (a (b (c d))) -> [Bool] -> Bool
satisfiable phi flags = not (provable (neg phi) flags)

osatisfiable :: (SigFeature a b (c d), Eq (a (b (c d)))) => [Bool] -> [Sequent] -> Formula (a (b (c d))) -> Bool
osatisfiable flags ec phi = not (oprovable flags ec (neg phi))

