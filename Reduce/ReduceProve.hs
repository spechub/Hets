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


reduceS :: String
reduceS = "Reduce"

-- | 
openReduceProofStatus :: String -> ProofStatus ()
openReduceProofStatus n = openProofStatus n reduceS ()

-- | 
reduceProver :: Prover Sign CMD Morphism () ()
reduceProver = mkProverTemplate reduceS () reduceProve

-- | splits a list of named sentences in the axioms and the sentences to be proven
getAxioms :: [Named CMD] -> ([Named CMD], [Named CMD])
getAxioms = partition isReduceAxiom

-- | checks whether a named sentence is a reduce axiom
isReduceAxiom :: Named CMD -> Bool
isReduceAxiom s = case sentence s of
                    Cmd {} -> isAxiom s


-- | 
reduceProve :: String -> Theory Sign CMD () -> a -> IO [ProofStatus ()]
reduceProve _ (Theory _ senMap) _freedefs = 
    let 
        namedCmds = toNamedList senMap
        (_, namedGoals) = getAxioms namedCmds
        cmds = map sentence namedGoals
    in
    do
      processCmds cmds
      return []

-- | connect to CAS, stepwise process the cmds
processCmds :: [CMD] -> IO [EXPRESSION]
processCmds cmds = do
  (inp,out,_,_) <- connectCAS
  processCmdsIntern (inp,out) cmds
  disconnectCAS (inp,out)
  return []

-- | internal function to process commands over an existing connection
processCmdsIntern :: (Handle,Handle) -> [CMD] -> IO [EXPRESSION]
processCmdsIntern _ [] = return []
processCmdsIntern (inp,out) (x:xs) = do
  res1 <- procCmd (inp,out) x
  ress <- processCmdsIntern (inp,out) xs
  return (res1 ++ ress)
