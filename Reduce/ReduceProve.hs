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

import Common.AS_Annotation
import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef)

import Data.List

import Logic.Prover

import Reduce.AS_BASIC_Reduce
import Reduce.Morphism
import Reduce.Reduce_Interface
import Reduce.Sign
import System.IO

-- as mkProverTemplate, but with additionally functionality to export lemmas
mkProverTemplateWithLemmaExport :: String -> sublogics
  -> (String -> theory -> [FreeDefMorphism sentence morphism]
      -> IO ([ProofStatus proof_tree],[(Named sentence, ProofStatus proof_tree)]))
  -> ProverTemplate theory sentence morphism sublogics proof_tree
mkProverTemplateWithLemmaExport str sl fct = Prover
    { proverName = str
    , proverSublogic = sl
    , proveGUI = Just $ \ s t fs -> do
                ps <- fct s t fs
                return ps
    , proveCMDLautomaticBatch = Nothing }

-- | the prover
reduceProver :: Prover Sign CMD Morphism () [EXPRESSION]
reduceProver = mkProverTemplateWithLemmaExport reduceS () reduceProve

-- | splits a list of named sentences into axioms and sentences to be proven
getAxioms :: [Named CMD] -> ([Named CMD], [Named CMD])
getAxioms = partition isReduceAxiom

-- | checks whether a named sentence is a reduce axiom
isReduceAxiom :: Named CMD -> Bool
isReduceAxiom s = case sentence s of
                    Cmd {} -> isAxiom s


{- | takes a theory name and a theory as input, starts the prover
  and returns a list of ProofStatus. -}
reduceProve :: String -> Theory Sign CMD [EXPRESSION] -> a
  -> IO ([ProofStatus [EXPRESSION]],[(Named sentence, ProofStatus proof_tree)])
reduceProve _ (Theory _ senMap) _freedefs =
    let
        namedCmds = toNamedList senMap
        (_, namedGoals) = getAxioms namedCmds
    in
    do
      proofinfos <- processCmds namedGoals
      return proofinfos

-- | connect to CAS, stepwise process the cmds
processCmds :: [Named CMD] -> IO ([ProofStatus [EXPRESSION]],[(Named sentence, ProofStatus proof_tree)])
processCmds cmds = do
  putStr "Connecting CAS.."
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  if noProg then do
    putStrLn "failed"
    putStrLn $ "Could not find reduce under " ++ reducecmd
    return ([],[])
    else do
    (inp, out, _, _) <- connectCAS reducecmd
    proofinfos <- processCmdsIntern (inp, out) cmds
    disconnectCAS (inp, out)
    return proofinfos

-- | internal function to process commands over an existing connection
processCmdsIntern :: (Handle, Handle) -> [Named CMD]
  -> IO ([ProofStatus [EXPRESSION]],[(Named sentence, ProofStatus proof_tree)])
processCmdsIntern _ [] = return ([],[])
processCmdsIntern (inp, out) (x : xs) = do
  (prooftree,newlemmas) <- procCmd (inp, out) x
  (prooftrees,newlemmas2) <- processCmdsIntern (inp, out) xs
  return (prooftree:prooftrees,newlemmas++newlemmas2)
