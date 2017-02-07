{- |
Module      :  ./TPTP/Prover/Leo2.hs
Description :  Interface for the Leo-II Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Leo2 (leo2) where

import TPTP.Prover.Common
import TPTP.Prover.ProofParser
import TPTP.Prover.ProverState
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Common.SZSOntology
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

import System.Exit

leo2 :: Prover Sign Sentence Morphism Sublogic ProofTree
leo2 = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "leo"

prover_name :: String
prover_name = "Leo-II"

sublogics :: Sublogic
sublogics = THF

runTheProver :: ProverState
                {- ^ logical part containing the input Sign and axioms and possibly
                goals that have been proved earlier as additional axioms -}
             -> GenericConfig ProofTree -- ^ configuration to use
             -> Bool -- ^ True means save TPTP file
             -> String -- ^ name of the theory in the DevGraph
             -> Named Sentence -- ^ goal to prove
             -> IO (ATPRetval, GenericConfig ProofTree)
                -- ^ (retval, configuration with proof status and complete output)
runTheProver proverState cfg saveTPTPFile theoryName namedGoal = do
  let proverTimeLimitS = show $ getTimeLimit cfg
      hardTimeLimitS = show $ hardTimeLimit cfg
      allOptions = [ "--proofoutput", "3"
                   , "--timeout", proverTimeLimitS
                   ]

  problemFileName <-
    prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name

  -- Leo-II runs for five minutes if a timeout of 30 seconds is set. Use the
  -- timeout executable to quit it by force it after a grace period.
  timeoutBin <- gnuTimeout
  (exitCode, out, wallTimeUsed) <-
    executeTheProver timeoutBin (hardTimeLimitS : binary_name :
                                 allOptions ++ [problemFileName])

  let timedOut = exitCode == ExitFailure 124
  let szsStatusLine = if timedOut then "Timeout" else findSZS out
  let resultedTimeUsed = wallTimeUsed
  let proofLines = filterProofLines out
  axiomsUsed <- if szsProved szsStatusLine || szsDisproved szsStatusLine
                then case axiomsFromProofObject proofLines of
                       (axiomNames, []) -> return axiomNames
                       (_, errs) -> do
                         putStrLn $ unlines errs
                         return $ getAxioms proverState
                else return $ getAxioms proverState
  let (atpRetval, resultedProofStatus) =
        atpRetValAndProofStatus cfg namedGoal resultedTimeUsed axiomsUsed
          szsStatusLine prover_name
  return (atpRetval, cfg { proofStatus = resultedProofStatus
                         , resultOutput = out
                         , timeUsed = resultedTimeUsed })
