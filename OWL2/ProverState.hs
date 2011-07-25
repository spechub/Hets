{- |
Module      :  $Header$
Description :  Interface to the OWL Ontology provers.
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

prover states for pellet and fact++
-}

module OWL2.ProverState where

import Logic.Prover

import OWL2.MS
import OWL2.Morphism
import OWL2.Sign
import OWL2.ManchesterPrint
import OWL2.XMLConversion

import Common.AS_Annotation

data ProverState = ProverState
    { ontologySign :: Sign,
      initialState :: [Named Axiom]
    } deriving Show

owlProverState :: Sign -> [Named Axiom]
    -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
    -> ProverState
owlProverState sig oSens _ = ProverState
    { ontologySign = sig,
    initialState = filter isAxiom oSens }

{- |
  Inserts a named OWL2 axiom into the prover state.
-}
insertOWLAxiom :: ProverState -- ^ prover state containing initial logical part
               -> Named Axiom -- ^ goal to add
               -> ProverState
insertOWLAxiom pps s = pps { initialState = initialState pps ++ [s] }

showOWLProblemS :: ProverState -> String -- ^ formatted output
showOWLProblemS pst =
    let namedSens = initialState pst
        sign = ontologySign pst
    in mkODoc sign (filter isAxiom namedSens)

{- |
  Pretty printing OWL goal for pellet or fact++
-}
showOWLProblem :: ProverState -- ^ prover state containing initial logical part
               -> Named Axiom -- ^ goal to print
               -> IO String -- ^ formatted output of the goal
showOWLProblem pst nGoal =
  let sign = ontologySign pst
  in return $ showOWLProblemS pst
       ++ "\n\nEntailments:\n\n" ++ show (printOWLBasicTheory (sign, [nGoal]))
