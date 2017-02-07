{- |
Module      :  ./TPTP/Prover/Isabelle.hs
Description :  Interface for Isabelle as an ATP.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Isabelle (isabelle) where

import TPTP.Prover.Common
import TPTP.Prover.ProofParser
import TPTP.Prover.ProverState
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

isabelle :: Prover Sign Sentence Morphism Sublogic ProofTree
isabelle = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "isabelle"

prover_name :: String
prover_name = "Isabelle"

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
  let proverTimeLimitS = show $ 1000 * getTimeLimit cfg
      allOptions = [ "tptp_isabelle"
                   , proverTimeLimitS
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
