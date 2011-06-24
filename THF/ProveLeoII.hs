{- |
Module      :  $Header$
Description :  Interface to the Leo-II theorem prover.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :

-}

module THF.ProveLeoII where

import Logic.Prover

import THF.Cons
import THF.ProverState

import Common.AS_Annotation
import Common.Result
import Common.ProofTree
import GUI.GenericATP
import Interfaces.GenericATPState
import qualified Control.Concurrent as Concurrent

import Proofs.BatchProcessing


leoIIName :: String
leoIIName = "Leo-II"

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover. -}
leoIIProver :: Prover SignTHF SentenceTHF MorphismTHF () ProofTree
leoIIProver = mkAutomaticProver leoIIName () leoIIGUI leoIICMDLautomaticBatch

leoIIHelpText :: String
leoIIHelpText =
  "No help available yet.\n" ++
  "email hets-devel@informatik.uni-bremen.de " ++
  "for more information.\n"

-- * Main prover functions

-- ** Utility functions

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> ATPFunctions SignTHF SentenceTHF MorphismTHF ProofTree ProverStateTHF
atpFun _ {- thName -} = ATPFunctions
  { initialProverState = initialProverStateTHF
  , atpTransSenName = error "missing atpTransSenName implementation"
  , atpInsertSentence = error "missing atpInsertSentence implementation"
  , goalOutput = error "missing goalOutput implementation"
  , proverHelpText = leoIIHelpText
  , batchTimeEnv = "HETS_LEOII_BATCH_TIME_LIMIT" --        <- IMPORTATN NOTE: ask Till about env vars.
  , fileExtensions = FileExtensions
      { problemOutput = ".thf"
      , proverOutput = ".leoII"
      , theoryConfiguration = ".lpcf" }
  , runProver = runLeoII
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI. LeoII specific functions are omitted by
  data type ATPFunctions.
-}
leoIIGUI :: String -- ^ theory name
    -> Theory SignTHF SentenceTHF ProofTree
    -> [FreeDefMorphism SentenceTHF MorphismTHF] -- ^ freeness constraints
    -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
leoIIGUI thName th freedefs =
    genericATPgui (atpFun thName) True leoIIName thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Darwin prover.
  Leo-II specific functions are omitted by data type ATPFunctions.
-}
leoIICMDLautomaticBatch
  :: Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory SignTHF SentenceTHF ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SentenceTHF MorphismTHF] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     {- ^ fst: identifier of the batch thread for killing it
     snd: MVar to wait for the end of the thread -}
leoIICMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar leoIIName thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
   Runs the Leo-II prover.
-}
runLeoII :: ProverStateTHF
           {- ^ logical part containing the input Sign and axioms and possibly
           goals that have been proved earlier as additional axioms -}
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> Named SentenceTHF -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runLeoII _ _ _ _ _ {- sps cfg saveTPTP thName nGoal -} =
        error "missing runLeoII implementation"
