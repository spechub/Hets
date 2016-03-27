{- |
Module      :  ./THF/ProverState.hs
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Data structures, initialising functions for Prover state and configurations.

-}

module THF.ProverState where

import Logic.Prover

import THF.As
import THF.Sign
import THF.Print

import Common.AS_Annotation

{- -----------------------------------------------------------------------------
Todos:
maybe use FreeDefMorphism in the ProverStateTHF
----------------------------------------------------------------------------- -}

data ProverStateTHF = ProverStateTHF
    { axioms :: [Named THFFormula]
    , signature :: SignTHF
    , freeDefs :: [FreeDefMorphism THFFormula MorphismTHF] }

-- Creates an initial THF prover state.
initialProverStateTHF :: SignTHF -> [Named THFFormula]
    -> [FreeDefMorphism THFFormula MorphismTHF]
    -> ProverStateTHF
initialProverStateTHF sign oSens freedefs = ProverStateTHF
    { axioms = filter isAxiom oSens
    , signature = sign
    , freeDefs = freedefs }

-- todo: investigate comment about negated axioms

-- Insert a Named SentenceTHF into the ProverStateTHF
insertSentenceTHF :: ProverStateTHF -> Named THFFormula -> ProverStateTHF
insertSentenceTHF ps ns = ps {axioms = ns : axioms ps}

showProblemTHF :: ProverStateTHF -> Named THFFormula -> [String] -> IO String
showProblemTHF ps goal _ = return $ show $ printProblemTHF (signature ps)
            (filter isAxiom (axioms ps)) goal

-- Get all axioms possibly used in a proof.
getAxioms :: ProverStateTHF -> [String]
getAxioms = map senAttr . filter isAxiom . axioms

-- FormulaRoles that are treated like axioms
thfAxioms :: [FormulaRole]
thfAxioms = [Axiom, Definition, Lemma, Theorem]
