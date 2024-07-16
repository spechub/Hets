module Main where

import Propositional.AS_BASIC_Propositional
import Propositional.Sublogic
import qualified Common.Id as Id

import qualified Data.Set as Set

import Control.Monad (unless)
import System.Exit (exitFailure)

import Debug.Trace


main :: IO ()
main = do
    let tests = [testPlain, testNNF, testCNF, testDNF, testCnfDnf, testHornF, testHornC]
    let testSuccess = and tests
    unless testSuccess exitFailure


-- We use the same range and token for all tests because it does not matter for our results

r :: Id.Range
r = Id.Range {Id.rangeToList = []}

t :: Id.Token
t = Id.Token {
    Id.tokStr = "",
    Id.tokPos = r
}


testPlain :: Bool
testPlain = testPos  && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip plainDesc $ map (Set.null . format . sl_form bottom) plain
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notPlainDesc $ map (not . Set.null . format . sl_form bottom) notPlain

        f1 = Negation (Disjunction [Predication t, Predication t] r) r
        f1' = "Plain_f1: ¬(A ∨ B)"
        f2 = Conjunction [f1, Negation (Predication t) r, f1] r
        f2' = "Plain_f2: (¬(A ∨ B)) ∧ ¬C ∧ (¬(D ∨ E))"
        f3 = Conjunction [Negation f1 r, f2] r
        f3' = "Plain_f3: ¬(¬(A ∨ B)) ∧ ((¬(A ∨ B)) ∧ ¬C ∧ (¬(D ∨ E)))"
        f4 = Implication (Negation (Predication t) r) (Predication t) r
        f4' = "Plain_f4: ¬A -> B"
        f5 = Equivalence f1 f2 r
        f5' = "Plain_f5: (A ∨ B) <-> ()"

        f11 = Conjunction [Predication t, Predication t] r
        f11' = "Plain_f11: A ∧ B"
        f12 = Disjunction [Negation (Predication t) r, Predication t] r
        f12' = "Plain_f12: ¬A ∨ B"
        f13 = Predication t
        f13' = "Plain_f13: A"
        f14 = Conjunction [f11, f12, f11] r
        f14' = "Plain_f14: (A ∧ B) ∧ (¬C ∨ D) ∧ (E ∧ F)"
        f15 = True_atom r
        f15' = "Plain_f15: True"

        plain = [f1, f2, f3, f4, f5]
        plainDesc = [f1', f2', f3', f4', f5']
        notPlain = [f11, f12, f13, f14, f15]
        notPlainDesc = [f11', f12', f13', f14', f15']

testNNF :: Bool
testNNF = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip nnfDesc $ map (isNNF . sl_form bottom) nnf
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notNnfDesc $ map (not . isNNF . sl_form bottom) notNnf

        f1 = Conjunction [Predication t, Predication t] r
        f1' = "Nnf_f1: A ∧ B"
        f2 = Disjunction [Negation (Predication t) r, Predication t] r
        f2' = "Nnf_f1: ¬C ∨ D"
        f3 = Predication t
        f3' = "Nnf_f1: A"
        f4 = Conjunction [f1, f2, f1] r
        f4' = "Nnf_f1: (A ∧ B) ∧ (¬C ∨ D) ∧ (E ∧ F)"
        f5 = True_atom r
        f5' = "Nnf_f1: True"

        f11 = Negation (Disjunction [f2, f2] r) r
        f11' = "Nnf_f11: ¬((¬A ∨ B) ∨ (¬C ∨ D))"
        f12 = Conjunction [f1, Negation f2 r, f1] r
        f12' = "Nnf_f12: (A ∧ B) ∧ ¬(C ∨ D) ∧ (A ∧ B)"
        f13 = Conjunction [Negation f1 r, f2] r
        f13' = "Nnf_f13: ¬(A ∧ B) ∧ (C ∨ D)"
        f14 = Implication (Predication t) (Predication t) r
        f14' = "Nnf_f14: A -> B"
        f15 = Equivalence f1 f2 r
        f15' = "Nnf_f15: A <-> B"

        nnf = [f1, f2, f3, f4, f5]
        nnfDesc = [f1', f2', f3', f4', f5']
        notNnf = [f11, f12, f13, f14, f15]
        notNnfDesc = [f11', f12', f13', f14', f15']

testCNF :: Bool
testCNF = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip cnfDesc $ map (isCNF . sl_form bottom) cnf
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notCnfDesc $ map (not . isCNF . sl_form bottom) notCnf

        f1 = Conjunction [Predication t, Predication t] r
        f1' = "Cnf_f1: A ∧ B"
        f2 = Disjunction [Negation (Predication t) r, Predication t] r
        f2' = "Cnf_f1: ¬A ∨ B"
        f3 = Predication t
        f3' = "Cnf_f1: A"
        f4 = Conjunction [f2, f2, f2] r
        f4' = "Cnf_f1: (¬A ∨ B) ∧ (¬C ∨ D) ∧ (¬E ∨ F)"
        f5 = True_atom r
        f5' = "Cnf_f1: True"

        f11 = Disjunction [f2, f2] r
        f11' = "Cnf_f1: (¬A ∨ B) ∨ (¬C ∨ D)"
        f12 = Conjunction [f1, f1] r
        f12' = "Cnf_f1: (A ∧ B) ∧ (C ∧ D)"
        f13 = Conjunction [f1, f2] r
        f13' = "Cnf_f1: (A ∧ B) ∧ (C ∨ D)"
        f14 = Implication (Predication t) (Predication t) r
        f14' = "Cnf_f1: A -> B"
        f15 = Equivalence f1 f2 r
        f15' = "Cnf_f1: A <-> B"

        cnf = [f1, f2, f3, f4, f5]
        cnfDesc = [f1', f2', f3', f4', f5']
        notCnf = [f11, f12, f13, f14, f15]
        notCnfDesc = [f11', f12', f13', f14', f15']

testDNF :: Bool
testDNF = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip dnfDesc $ map (isDNF . sl_form bottom) dnf
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notDnfDesc $ map (not . isDNF . sl_form bottom) notDnf

        f1 = Conjunction [Predication t, Predication t] r
        f1' = "Dnf_f1: A ∧ B"
        f2 = Disjunction [Negation (Predication t) r, Predication t] r
        f2' = "Dnf_f2: ¬A ∨ B"
        f3 = Predication t
        f3' = "Dnf_f3: A"
        f4 = Disjunction [f1, f1, f1] r
        f4' = "Dnf_f4: (A ∧ B) ∨ (C ∧ D) ∨ (E ∧ F)"
        f5 = True_atom r
        f5' = "Dnf_f5: True"

        f11 = Conjunction [f2, f2] r
        f11' = "Dnf_f11:(¬A ∨ B) ∧ (¬C ∨ D)"
        f12 = Disjunction [f1, f2] r
        f12' = "Dnf_f12: (A ∧ B) ∨ (¬C ∨ D)"
        f13 = Conjunction [f1, f2] r
        f13' = "Dnf_f13: (A ∧ B) ∧ (¬C ∨ D)"
        f14 = Implication (Predication t) (Predication t) r
        f14' = "Dnf_f14: A -> B"
        f15 = Equivalence f1 f2 r
        f15' = "Dnf_f15: A <-> B"

        dnf = [f1, f2, f3, f4, f5]
        dnfDesc = [f1', f2', f3', f4', f5']
        notDnf = [f11, f12, f13, f14, f15]
        notDnfDesc = [f11', f12', f13', f14', f15']

testCnfDnf :: Bool
testCnfDnf = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip cnfDnfDesc $ map ((\x -> isCNF x && isDNF x) . sl_form bottom) cnfDnf
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notCnfDnfDesc $ map ((\x -> not (isCNF x && isDNF x)) . sl_form bottom) notCnfDnf

        f1 = Conjunction [Predication t, Predication t] r
        f1' = "CnfDnf_f1: A ∧ B"
        f2 = Disjunction [Negation (Predication t) r, Predication t] r
        f2' = "CnfDnf_f1: ¬A ∨ B"
        f3 = Predication t
        f3' = "CnfDnf_f1: A"
        f4 = Negation (Predication t) r
        f4' = "CnfDnf_f1: ¬A"
        f5 = True_atom r
        f5' = "CnfDnf_f1: True"

        f11 = Conjunction [f2, f2] r
        f11' = "CnfDnf_f11: (¬A ∨ B) ∧ (¬C ∨ D)"
        f12 = Disjunction [f1, f1] r
        f12' = "CnfDnf_f12: (A ∧ B) ∨ (C ∧ D)"
        f13 = Conjunction [f1, f2] r
        f13' = "CnfDnf_f13: (A ∧ B) ∧ (¬C ∨ D)"
        f14 = Implication (Predication t) (Predication t) r
        f14' = "CnfDnf_f14: A -> B"
        f15 = Equivalence f1 f2 r
        f15' = "CnfDnf_f15: A <-> B"

        cnfDnf = [f1, f2, f3, f4, f5]
        cnfDnfDesc = [f1', f2', f3', f4', f5']
        notCnfDnf = [f11, f12, f13, f14, f15]
        notCnfDnfDesc = [f11', f12', f13', f14', f15']

testHornC :: Bool
testHornC = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip hornDesc $ map (isHC . sl_form bottom) hornFormulas
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notHornDesc $ map (not . isHC . sl_form bottom) notHornFormulas

        f1 = True_atom r
        f1' = "HornC_f1: True"
        f2 = Negation (Predication t) r
        f2' = "HornC_f2: ¬A"
        f3 = Conjunction [Disjunction [Negation (Predication t) r, Predication t] r] r
        f3' = "HornC_f3: ∧(¬A ∨ B)"
        f4 = Conjunction [Disjunction [Negation (Predication t) r, Negation (Predication t) r] r] r
        f4' = "HornC_f4: ∧(¬A ∨ ¬B)"
        f5 = Conjunction [Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t] r, Disjunction [Negation (Predication t) r, Predication t] r, f1] r
        f5' = "HornC_f5: (¬A ∨ ¬B ∨ ¬C ∨ ¬D ∨ E) ∧ (¬F ∨ G) ∧ (H -> I)"
        f6 = Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t] r
        f6' = "HornC_f6: ¬A ∨ ¬B ∨ ¬C ∨ ¬D ∨ E"

        f11 = Implication (Predication t) (Predication t) r
        f11' = "HornC_f11: A -> B"
        f12 = Implication (Conjunction [Predication t, Predication t, Predication t, True_atom r] r) (Predication t) r
        f12' = "HornC_f12: (A ∧ B ∧ C ∧ True) -> D"
        f13 = Disjunction [True_atom r, False_atom  r] r
        f13' = "HornC_f13: True ∨ False"
        f14 = Conjunction [f11, f2] r
        f14' = "HornC_f14: ((A ∨ G) -> B) ∧ ((C ∧ D ∧ E ∧ True) -> F)"
        f15 = Conjunction [Disjunction [Predication t, Predication t] r] r
        f15' = "HornC_f15: ∧(A ∨ B)"
        f16 = Conjunction [Disjunction [Predication t, Predication t, Negation (Predication t) r, Negation (Predication t) r, Predication t] r, Disjunction [Negation (Predication t) r, Predication t] r, f1] r
        f16' = "HornC_f16: (A ∨ B ∨ ¬C ∨ ¬D ∨ E) ∧ (¬F ∨ G) ∧ (H -> I)"
        f17 = Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t, Predication t] r
        f17' = "HornC_f17: ¬A ∨ ¬B ∨ ¬C ∨ D ∨ E"

        hornFormulas = [f1, f2, f3, f4, f5, f6]
        hornDesc = [f1', f2', f3', f4', f5', f6']
        notHornFormulas = [f11, f12, f13, f14, f15, f16, f17]
        notHornDesc = [f11', f12', f13', f14', f15', f16', f17']

testHornF :: Bool
testHornF = testPos && testNeg
    where
        testPos = all (\x -> printIfFailed (snd x) (fst x)) $ zip hornDesc $ map (isHF . sl_form bottom) hornFormulas
        testNeg = all (\x -> printIfFailed (snd x) (fst x)) $ zip notHornDesc $ map (not . isHF . sl_form bottom) notHornFormulas

        f1 = Implication (Predication t) (Predication t) r
        f1' = "HornF_f1: A -> B"
        f2 = Implication (Conjunction [Predication t, Predication t, Predication t, True_atom r] r) (Predication t) r
        f2' = "HornF_f2: (A ∧ B ∧ C ∧ True) -> D"
        f3 = True_atom r
        f3' = "HornF_f3: True"
        f4 = Negation (Predication t) r
        f4' = "HornF_f4: ¬A"
        f5 = Conjunction [f1, f2] r
        f5' = "HornF_f5: (A -> B) ∧ ((C ∧ D ∧ E ∧ True) -> F)"
        f6 = Conjunction [Disjunction [Negation (Predication t) r, Predication t] r] r
        f6' = "HornF_f6: ∧(¬A ∨ B)"
        f7 = Conjunction [Disjunction [Negation (Predication t) r, Negation (Predication t) r] r] r
        f7' = "HornF_f7: ∧(¬A ∨ ¬B)"
        f8 = Conjunction [Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t] r, Disjunction [Negation (Predication t) r, Predication t] r, f1] r
        f8' = "HornF_f8: (¬A ∨ ¬B ∨ ¬C ∨ ¬D ∨ E) ∧ (¬F ∨ G) ∧ (H -> I)"
        f9 = Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t] r
        f9' = "HornF_f9: ¬A ∨ ¬B ∨ ¬C ∨ ¬D ∨ E"

        f11 = Implication (Disjunction [Predication t, Predication t] r) (Predication t) r
        f11' = "HornF_f11: (A ∨ B) -> C"
        f12 = Implication (Conjunction [Predication t, Negation (Predication t) r, Predication t, True_atom r] r) (Predication t) r
        f12' = "HornF_f12: (A ∧ ¬B ∧ C ∧ True) -> D"
        f13 = Disjunction [True_atom r, False_atom  r] r
        f13' = "HornF_f13: True ∨ False"
        f14 = Conjunction [f11, f2] r
        f14' = "HornF_f14: ((A ∨ G) -> B) ∧ ((C ∧ D ∧ E ∧ True) -> F)"
        f15 = Conjunction [Disjunction [Predication t, Predication t] r] r
        f15' = "HornF_f15: ∧(A ∨ B)"
        f16 = Conjunction [Disjunction [Predication t, Predication t, Negation (Predication t) r, Negation (Predication t) r, Predication t] r, Disjunction [Negation (Predication t) r, Predication t] r, f1] r
        f16' = "HornF_f16: (A ∨ B ∨ ¬C ∨ ¬D ∨ E) ∧ (¬F ∨ G) ∧ (H -> I)"
        f17 = Disjunction [Negation (Predication t) r, Negation (Predication t) r, Negation (Predication t) r, Predication t, Predication t] r
        f17' = "HornF_f17: ¬A ∨ ¬B ∨ ¬C ∨ D ∨ E"

        hornFormulas = [f1, f2, f3, f4, f5, f6, f7, f8, f9]
        hornDesc = [f1', f2', f3', f4', f5', f6', f7', f8', f9']
        notHornFormulas = [f11, f12, f13, f14, f15, f16, f17]
        notHornDesc = [f11', f12', f13', f14', f15', f16', f17']


-- helper

printIfFailed :: Bool -> String -> Bool
printIfFailed correct desc =
    if not correct
        then trace ("failed in test for: " ++ desc) correct
        else correct
