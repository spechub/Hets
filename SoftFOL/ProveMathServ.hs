{- |
Module      :  $Header$
Description :  Interface for the MathServe broker.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the MathServe broker which calls different ATP systems,
uses GUI.GenericATP.

-}

{-
    To do:
    - check why an internal error during batch mode running does not invoke
      an error window. Also the proving won't stop.
-}

module SoftFOL.ProveMathServ
  ( mathServBroker
  , mathServBrokerCMDLautomaticBatch
  ) where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.MathServMapping
import SoftFOL.MathServParsing
import SoftFOL.ProverState

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent
import qualified Control.Exception as Exception

import GUI.GenericATP
import Interfaces.GenericATPState
import Proofs.BatchProcessing

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
mathServBroker :: Prover Sign Sentence SoftFOLMorphism () ProofTree
mathServBroker = mkAutomaticProver brokerName () mathServBrokerGUI
  mathServBrokerCMDLautomaticBatch

mathServHelpText :: String
mathServHelpText =
  "No help for MathServ available.\n"

-- * Main prover functions

-- ** Utility functions

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> ATPFunctions Sign Sentence SoftFOLMorphism ProofTree SoftFOLProverState
atpFun thName = ATPFunctions
    { initialProverState = spassProverState,
      atpTransSenName = transSenName,
      atpInsertSentence = insertSentenceGen,
      goalOutput = showTPTPProblem thName,
      proverHelpText = mathServHelpText,
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions {problemOutput = ".tptp",
                                      proverOutput = ".spass",
                                      theoryConfiguration = ".spcf"},
      runProver = runMSBroker,
      createProverOptions = extraOpts}

-- ** GUI

{- |
  Invokes the generic prover GUI. SoftFOL specific functions are omitted by
  data type ATPFunctions.
-}
mathServBrokerGUI :: String -- ^ theory name
                  -> Theory Sign Sentence ProofTree
                  {- ^ theory consisting of a SoftFOL.Sign.Sign
                  and a list of Named SoftFOL.Sign.Sentence -}
                  -> [FreeDefMorphism SPTerm SoftFOLMorphism]
                  -- ^ freeness constraints
                  -> IO [ProofStatus ProofTree]
                     -- ^ proof status for each goal
mathServBrokerGUI thName th freedefs =
    genericATPgui (atpFun thName) False (proverName mathServBroker) thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the MathServe Broker.
  MathServ specific functions are omitted by data type ATPFunctions.
-}
mathServBrokerCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Sentence ProofTree {- ^ theory consisting of a
           'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence' -}
        -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId, Concurrent.MVar ())
           {- ^ fst: identifier of the batch thread for killing it
           snd: MVar to wait for the end of the thread -}
mathServBrokerCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName mathServBroker) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree


{- |
  Runs the MathServ broker and returns GUI proof status and prover
  configuration with  proof status and complete prover output.
-}
runMSBroker :: SoftFOLProverState
            {- ^ logical part containing the input Sign and axioms and possibly
            goals that have been proved earlier as additional axioms -}
            -> GenericConfig ProofTree -- ^ configuration to use
            -> Bool -- ^ True means save TPTP file
            -> String -- ^ name of the theory in the DevGraph
            -> AS_Anno.Named SPTerm -- ^ goal to prove
            -> IO (ATPRetval, GenericConfig ProofTree)
            -- ^ (retval, configuration with proof status and complete output)
runMSBroker sps cfg saveTPTP thName nGoal =
  Exception.catch (do
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg
            ++ ['[' : brokerName ++ "]"]
    when saveTPTP
        (writeFile (thName ++ '_' : AS_Anno.senAttr nGoal ++ ".tptp") prob)
    mathServOut <- callMathServ
        MathServCall {mathServService = Broker,
                     mathServOperation = ProblemOpt,
                     problem = prob,
                     proverTimeLimit = configTimeLimit cfg,
                     extraOptions = Nothing}
    msResponse <- parseMathServOut mathServOut
    return (mapMathServResponse msResponse cfg nGoal $
            proverName mathServBroker))
   $ excepToATPResult (proverName mathServBroker) $ AS_Anno.senAttr nGoal
