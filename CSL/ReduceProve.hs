{- |
Module      :  ./CSL/ReduceProve.hs
Description :  interface to Reduce CAS
Copyright   :  (c) Dominik Dietrich, DFKI Bremen, 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Dominik.Dietrich@dfki.de
Stability   :  provisional
Portability :  portable

Interface for Reduce CAS system.
-}

module CSL.ReduceProve where

import Common.AS_Annotation

import Data.List

import Logic.Prover

import CSL.AS_BASIC_CSL
import CSL.Morphism
import CSL.Reduce_Interface
import CSL.Sign

-- as mkProverTemplate, but with additionally functionality to export lemmas
mkProverTemplateWithLemmaExport :: String -> sublogics
  -> (String -> theory -> [FreeDefMorphism sentence morphism]
      -> IO ( [ProofStatus proof_tree]
            , [(Named sentence, ProofStatus proof_tree)]))
  -> ProverTemplate theory sentence morphism sublogics proof_tree
mkProverTemplateWithLemmaExport str sl fct = Prover
    { proverName = str
    , proverUsable = fmap (either (const Nothing) Just) lookupRedShellCmd
    , proverSublogic = sl
    , proveGUI = Just $ \ s t fs -> fct s t fs
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
                    _ -> False -- TODO: implement


{- | takes a theory name and a theory as input, starts the prover
  and returns a list of ProofStatus. -}
reduceProve :: String -> Theory Sign CMD [EXPRESSION] -> a
  -> IO ([ProofStatus [EXPRESSION]], [(Named CMD, ProofStatus [EXPRESSION])])
reduceProve _ (Theory _ senMap) _freedefs =
    let
        namedCmds = toNamedList senMap
        (_, namedGoals) = getAxioms namedCmds
    in processCmds namedGoals

-- | connect to CAS, stepwise process the cmds
processCmds :: [Named CMD]
  -> IO ([ProofStatus [EXPRESSION]], [(Named CMD, ProofStatus [EXPRESSION])])
processCmds cmds = do
  putStr "Connecting CAS.."
  sc <- lookupRedShellCmd
  case sc of
    Right reducecmd ->
        do
          putStrLn "failed"
          putStrLn $ "Could not find reduce under " ++ reducecmd
          return ([], [])
    Left reducecmd ->
        do
          (inpt, out, _, pid) <- connectCAS reducecmd
          proofinfos <- processCmdsIntern (inpt, out, pid) cmds
          disconnectCAS (inpt, out, pid)
          return proofinfos


-- | internal function to process commands over an existing connection
processCmdsIntern :: Session a => a -> [Named CMD]
  -> IO ([ProofStatus [EXPRESSION]], [(Named CMD, ProofStatus [EXPRESSION])])
processCmdsIntern _ [] = return ([], [])
processCmdsIntern sess (x : xs) = do
  (prooftree, newlemmas) <- procCmd sess x
  (prooftrees, newlemmas2) <- processCmdsIntern sess xs
  return (prooftree : prooftrees, newlemmas ++ newlemmas2)
