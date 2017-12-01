{- |
Module      :  ./TPTP/Prover/EProver.hs
Description :  Interface for the E Theorem Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.EProver (eprover) where

import TPTP.Prover.Common
import TPTP.Prover.EProver.ProofParser
import TPTP.Prover.ProofParser
import TPTP.Prover.ProverState
import TPTP.Morphism
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Common.SZSOntology
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

import Data.Time.LocalTime
import Data.Time.Clock

eprover :: Prover Sign Sentence Morphism Sublogic ProofTree
eprover = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "eprover"

prover_name :: String
prover_name = "EProver"

sublogics :: Sublogic
sublogics = FOF

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
      allOptions = [ "--tstp-format"
                   , "--proof-object"
                   , "--output-level=0"
                   , "--auto"
                   , "--cpu-limit=" ++ proverTimeLimitS
                   , "--memory-limit=4096"
                   ]

  problemFileName <-
    prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name

  (_, out, wallTimeUsed) <-
    executeTheProver binary_name (allOptions ++ [problemFileName])

  let szsStatusLine = findSZS out
  let reportedTimeUsed = parseTimeUsed out
  let resultedTimeUsed =
        if reportedTimeUsed == -1
        then wallTimeUsed
        else timeToTimeOfDay $ secondsToDiffTime $
               toInteger reportedTimeUsed
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
