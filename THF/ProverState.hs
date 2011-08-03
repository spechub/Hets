{- |
Module      :  $Header$
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
import THF.Cons
import THF.Sign
import THF.Print

import Common.AS_Annotation

--------------------------------------------------------------------------------
-- Todos:
--      * maybe use FreeDefMorphism in the ProverStateTHF
--------------------------------------------------------------------------------

-- * Data structures

data ProverStateTHF = ProverStateTHF
    { axioms    :: [Named SentenceTHF]
    , signature :: SignTHF
    , freeDefs  :: [FreeDefMorphism SentenceTHF MorphismTHF] }

-- * THF specific functions for prover GUI

{- |
  Creates an initial THF prover state.
-}
initialProverStateTHF :: SignTHF -> [Named SentenceTHF]
    -> [FreeDefMorphism SentenceTHF MorphismTHF]
    -> ProverStateTHF
initialProverStateTHF sign oSens freedefs = ProverStateTHF
    { axioms = filter isAxiom oSens
    , signature = sign
    , freeDefs = freedefs }

insertSentenceTHF :: ProverStateTHF -> Named SentenceTHF -> ProverStateTHF
insertSentenceTHF ps ns = ps {axioms = (checkAxiom ns) : axioms ps}

showProblemTHF :: ProverStateTHF -> Named SentenceTHF -> [String] -> IO String
showProblemTHF ps goal _ = return $ show $ printProblemTHF (signature ps)
            (filter isAxiom (map checkAxiom (axioms ps))) goal

-- | get all axioms possibly used in a proof
getAxioms :: ProverStateTHF -> [String]
getAxioms = map (senAttr) . filter isAxiom . map checkAxiom . axioms

-- be carefull with negated_conjectures
-- eventually negated conjectures should be negated before the are transformed
-- into Axioms or Theorems
checkAxiom :: Named SentenceTHF -> Named SentenceTHF
checkAxiom ns =
    let sen = sentence ns
    in if isAxiom ns
       then if elem (senRole sen) thfAxioms then ns
            else if wasTheorem ns
                 then ns { sentence = sen { senRole = Theorem } }
                 else ns { sentence = sen { senRole = Axiom } }
       else if elem (senRole sen) [Conjecture, Negated_Conjecture] then ns
            else ns { sentence = sen { senRole = Conjecture } }

thfAxioms :: [FormulaRole]
thfAxioms = [Axiom, Definition, Lemma, Theorem]


