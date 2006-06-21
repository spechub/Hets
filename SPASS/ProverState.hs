{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Data structures and initialising functions for Prover state and configurations.

-}

module SPASS.ProverState where

import SPASS.Sign
import SPASS.Conversions
import SPASS.Translate
import SPASS.PrintTPTP
import SPASS.PrintDFG

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.PrettyPrint

-- * Data structures

data SPASSProverState = SPASSProverState
    { initialLogicalPart :: SPLogicalPart}

-- * SPASS specific functions for prover GUI

{- |
  Creates an initial SPASS prover state with logical part.
-}
spassProverState :: Sign -- ^ SPASS signature
                 -> [AS_Anno.Named SPTerm] -- ^ list of named SPASS terms 
                                           --   containing axioms
                 -> SPASSProverState
spassProverState sign oSens' = SPASSProverState{
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axioms)}
  where nSens = prepareSenNames transSenName oSens'
        axioms = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SPASS term into SPASS prover state.
-}
insertSentenceGen :: SPASSProverState -- ^ prover state containing
                                      --   initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to add
                  -> SPASSProverState
insertSentenceGen pst s = pst{initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SPASS goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to print
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst nGoal = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  return $ show $ printDFG prob

{- |
  Pretty printing SPASS goal in TPTP format.
-}
showTPTPProblem :: String -- ^ theory name
                -> SPASSProverState -- ^ prover state containing
                                    --   initial logical part
                -> AS_Anno.Named SPTerm -- ^ goal to print
                -> IO String -- ^ formatted output of the goal
showTPTPProblem thName pst nGoal = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  return $ show $ printTPTP prob
