{- |
Module      :  $Header$
Description :  Interface for the MathServe broker.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
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

module SoftFOL.ProveMathServ ( mathServBroker
                           , mathServBrokerGUI
                           , mathServBrokerCMDLautomatic
                           , mathServBrokerCMDLautomaticBatch) where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.MathServMapping
import SoftFOL.MathServParsing
import SoftFOL.ProverState

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result

import qualified Control.Concurrent as Concurrent
import qualified Control.Exception as Exception

import HTk

import GUI.GenericATP
import GUI.GenericATPState
import Proofs.BatchProcessing

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
mathServBroker :: Prover Sign Sentence () ATP_ProofTree
mathServBroker = (mkProverTemplate brokerName () mathServBrokerGUI)
    { proveCMDLautomatic = Just mathServBrokerCMDLautomatic
    , proveCMDLautomaticBatch = Just mathServBrokerCMDLautomaticBatch }

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
       -> ATPFunctions Sign Sentence ATP_ProofTree SoftFOLProverState
atpFun thName = ATPFunctions
    { initialProverState = spassProverState,
      atpTransSenName = transSenName,
      atpInsertSentence = insertSentenceGen,
      goalOutput = showTPTPProblem thName,
      proverHelpText = mathServHelpText,
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".tptp",
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
                  -> Theory Sign Sentence ATP_ProofTree
                  -- ^ theory consisting of a SoftFOL.Sign.Sign
                  --   and a list of Named SoftFOL.Sign.Sentence
                  -> IO([Proof_status ATP_ProofTree])
                     -- ^ proof status for each goal
mathServBrokerGUI thName th =
    genericATPgui (atpFun thName) False (prover_name mathServBroker) thName th $
                  ATP_ProofTree ""

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  MathServ specific functions are omitted by data type ATPFunctions.
-}
mathServBrokerCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status ATP_ProofTree]))
           -- ^ Proof status for goals and lemmas
mathServBrokerCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name mathServBroker) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the MathServe Broker.
  MathServ specific functions are omitted by data type ATPFunctions.
-}
mathServBrokerCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ATP_ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
mathServBrokerCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name mathServBroker) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")


{- |
  Runs the MathServ broker and returns GUI proof status and prover
  configuration with  proof status and complete prover output.
-}
runMSBroker :: SoftFOLProverState
            -- ^ logical part containing the input Sign and axioms and possibly
            --   goals that have been proved earlier as additional axioms
            -> GenericConfig ATP_ProofTree -- ^ configuration to use
            -> Bool -- ^ True means save TPTP file
            -> String -- ^ name of the theory in the DevGraph
            -> AS_Anno.Named SPTerm -- ^ goal to prove
            -> IO (ATPRetval, GenericConfig ATP_ProofTree)
            -- ^ (retval, configuration with proof status and complete output)
runMSBroker sps cfg saveTPTP thName nGoal = do
--    putStrLn ("running MathServ Broker...")
  Exception.catch (do
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg
            ++ ['[':brokerName++"]"]
    when saveTPTP
        (writeFile (thName++'_':AS_Anno.senAttr nGoal++".tptp") prob)
    mathServOut <- callMathServ
        MathServCall{mathServService = Broker,
                     mathServOperation = ProblemOpt,
                     problem = prob,
                     proverTimeLimit = tLimit,
                     extraOptions = Nothing}
    msResponse <- parseMathServOut mathServOut
    return (mapMathServResponse msResponse cfg nGoal $
            prover_name mathServBroker))
    (excepToATPResult (prover_name mathServBroker) nGoal)
  where
    tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg
