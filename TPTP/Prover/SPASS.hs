{- |
Module      :  ./TPTP/Prover/SPASS.hs
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.SPASS (spass) where

import TPTP.Prover.Common
import TPTP.Prover.SPASS.ProofParser
import TPTP.Prover.ProverState
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

import Data.List

spass :: Prover Sign Sentence Morphism Sublogic ProofTree
spass = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "SPASS"

prover_name :: String
prover_name = "SPASS"

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
      allOptions = [ "-TPTP"
                   , "-DocProof"
                   , "-TimeLimit=" ++ proverTimeLimitS
                   ]

  problemFileName <-
    prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name

  (_, out, _) <-
    executeTheProver binary_name (allOptions ++ [problemFileName])

  let (mResult, axiomsUsed, outputExists, resultedTimeUsed) =
        parseOutput namedGoal out
  let (defaultProofStatus, provedStatus, disprovedStatus) =
        proofStatuses cfg namedGoal resultedTimeUsed axiomsUsed prover_name
  let (atpRetval, resultedProofStatus) = case mResult of
        Nothing -> (ATPError $ errorMessage outputExists, defaultProofStatus)
        Just result
          | isInfixOf "Proof found." result -> (ATPSuccess, provedStatus)
          | isInfixOf "Completion found." result -> (ATPSuccess, disprovedStatus)
          | isInfixOf "Ran out of time." result ->
              (ATPTLimitExceeded, defaultProofStatus)
        _ -> (ATPSuccess, defaultProofStatus)
  return (atpRetval, cfg { proofStatus = resultedProofStatus
                         , resultOutput = out
                         , timeUsed = resultedTimeUsed })
  where
    errorMessage :: Bool -> String
    errorMessage outputExists =
      "No " ++
        (if outputExists then "result" else "output") ++
        " of " ++ prover_name ++ " found."
