{- |
Module      :  $Header$
Description :  interface to Reduce CAS
Copyright   :  (c) Dominik Dietrich, DFKI Bremen, 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Dominik.Dietrich@dfki.de
Stability   :  provisional
Portability :  portable

Interface for Reduce CAS system.
-}

module Reduce.ReduceProve where

import Logic.Prover
import Reduce.Sign
import Reduce.AS_BASIC_Reduce
import Common.AS_Annotation
import Reduce.Morphism
import Reduce.Reduce_Interface
import Data.List
import System.IO


-- | 
reduceProver :: Prover Sign CMD Morphism () [EXPRESSION]
reduceProver = mkProverTemplate reduceS () reduceProve

-- | splits a list of named sentences in the axioms and the sentences to be proven
getAxioms :: [Named CMD] -> ([Named CMD], [Named CMD])
getAxioms = partition isReduceAxiom

-- | checks whether a named sentence is a reduce axiom
isReduceAxiom :: Named CMD -> Bool
isReduceAxiom s = case sentence s of
                    Cmd {} -> isAxiom s


-- | takes a theory name and a theory as input, starts the prover and returns a list of ProofStatus
reduceProve :: String -> Theory Sign CMD [EXPRESSION] -> a -> IO [ProofStatus [EXPRESSION]]
reduceProve _ (Theory _ senMap) _freedefs = 
    let 
        namedCmds = toNamedList senMap
        (_, namedGoals) = getAxioms namedCmds
    in
    do
      proofinfos <- processCmds namedGoals
      putStrLn $ "Proof infos are : " ++ (show proofinfos)
      return proofinfos

-- | connect to CAS, stepwise process the cmds
processCmds :: [Named CMD] -> IO [ProofStatus [EXPRESSION]]
processCmds cmds = do
  (inp,out,_,_) <- connectCAS
  proofinfos <- processCmdsIntern (inp,out) cmds
  disconnectCAS (inp,out)
  return proofinfos

-- | internal function to process commands over an existing connection
processCmdsIntern :: (Handle,Handle) -> [Named CMD] -> IO [ProofStatus [EXPRESSION]]
processCmdsIntern _ [] = return []
processCmdsIntern (inp,out) (x:xs) = do
  res1 <- procCmd (inp,out) x
  ress <- processCmdsIntern (inp,out) xs
  return (res1 : ress)
