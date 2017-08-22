{- |
Module      :  ./TPTP/Prover/Satallax.hs
Description :  Interface for the Satallax Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Satallax (satallax) where

import TPTP.Prover.Common
import TPTP.Prover.ProofParser
import TPTP.Prover.ProverState
import TPTP.Morphism
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

satallax :: Prover Sign Sentence Morphism Sublogic ProofTree
satallax = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "satallax"

prover_name :: String
prover_name = "Satallax"

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
      allOptions = [ "-p", "tstp"
                   , "-t", proverTimeLimitS
                   ]

  problemFileName <-
    prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name

  (_, out, wallTimeUsed) <-
    executeTheProver binary_name (allOptions ++ [problemFileName])

  let szsStatusLine = findSZS out
  let resultedTimeUsed = wallTimeUsed
  let axiomsUsed = getAxioms proverState
  let (atpRetval, resultedProofStatus) =
        atpRetValAndProofStatus cfg namedGoal resultedTimeUsed axiomsUsed
          szsStatusLine prover_name
  return (atpRetval, cfg { proofStatus = resultedProofStatus
                         , resultOutput = out
                         , timeUsed = resultedTimeUsed })
