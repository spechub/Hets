{- |
Module      :  ./TPTP/Prover/Vampire.hs
Description :  Interface for the Vampire theorem prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Vampire (vampire) where

import TPTP.Prover.Common
import TPTP.Prover.Vampire.ProofParser
import TPTP.Prover.ProofParser hiding (filterProofLines)
import TPTP.Prover.ProverState
import TPTP.Morphism
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Common.SZSOntology
import Interfaces.GenericATPState hiding (proverState)
import Logic.Prover hiding (proofLines)

vampire :: Prover Sign Sentence Morphism Sublogic ProofTree
vampire = mkProver binary_name prover_name sublogics runTheProver

binary_name :: String
binary_name = "vampire"

prover_name :: String
prover_name = "Vampire"

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
      allOptions = [ "--input_syntax", "tptp"
                   , "--proof", "tptp"
                   , "--output_axiom_names", "on"
                   , "--time_limit", proverTimeLimitS
                   , "--memory_limit", "4096"
                   , "--mode", "vampire"
                   ]

  problemFileName <-
    prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name

  (_, out, _) <-
    executeTheProver binary_name (allOptions ++ [problemFileName])
  let szsStatusLine = parseStatus out
  let resultedTimeUsed = parseTimeUsed out
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
