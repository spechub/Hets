{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover using MathServ.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{-
    To do:
    - check why an internal error during batch mode running does not invoke
      an error window. Also the proving won't stop.
-}

module SPASS.ProveMathServ (mathServBroker,mathServBrokerGUI,
            mathServBrokerCMDLautomatic,mathServBrokerCMDLautomaticBatch) where

import Logic.Prover

import SPASS.Sign
import SPASS.Translate
import SPASS.MathServMapping
import SPASS.MathServParsing
import SPASS.ProverState

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result

import Data.IORef
-- import Data.List
-- import Data.Maybe
import qualified Control.Concurrent as Concurrent

import HTk

import GUI.GenericATP
import GUI.GenericATPState
import Proofs.BatchProcessing

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
mathServBroker :: Prover Sign Sentence ATP_ProofTree
mathServBroker = emptyProverTemplate
         { prover_name = brokerName,
           prover_sublogic = "SoftFOL",
           proveGUI = Just mathServBrokerGUI,
           proveCMDLautomatic = Just mathServBrokerCMDLautomatic,
           proveCMDLautomaticBatch = Just mathServBrokerCMDLautomaticBatch
         }

spassHelpText :: String
spassHelpText =
  "No help yet available.\n" ++
  "Ask Klaus Lüttich (luettich@informatik.uni-bremen.de) for more information.\n"



-- * Main prover functions

-- ** Utility functions

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Sentence ATP_ProofTree SPASSProverState
atpFun thName = ATPFunctions
    { initialProverState = spassProverState,
      atpTransSenName = transSenName,
      atpInsertSentence = insertSentenceGen,
      goalOutput = showTPTPProblem thName,
      proverHelpText = spassHelpText,
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
                  -- ^ theory consisting of a SPASS.Sign.Sign
                  --   and a list of Named SPASS.Sign.Sentence
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
        -> Theory Sign Sentence ATP_ProofTree -- ^ theory consisting of a signature
                                           --   and a list of Named sentence
        -> IO (Result.Result ([Proof_status ATP_ProofTree]))
           -- ^ Proof status for goals and lemmas
mathServBrokerCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name mathServBroker) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the SPASS prover.
  MathServ specific functions are omitted by data type ATPFunctions.
-}
mathServBrokerCMDLautomaticBatch :: 
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> IORef (Result.Result [Proof_status ATP_ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree -- ^ theory consisting of a
           --   'SPASS.Sign.Sign' and a list of Named 'SPASS.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
mathServBrokerCMDLautomaticBatch inclProvedThs saveProblem_batch resultRef
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultRef (prover_name mathServBroker) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")


{- |
  Runs the MathServ broker and returns GUI proof status and prover
  configuration with  proof status and complete prover output.
-}
runMSBroker :: SPASSProverState
            -- ^ logical part containing the input Sign and axioms and possibly
            --   goals that have been proved earlier as additional axioms
            -> GenericConfig ATP_ProofTree -- ^ configuration to use
            -> Bool -- ^ True means save TPTP file
            -> String -- ^ name of the theory in the DevGraph
            -> AS_Anno.Named SPTerm -- ^ goal to prove
            -> IO (ATPRetval, GenericConfig ATP_ProofTree)
            -- ^ (retval, configuration with proof status and complete output)
runMSBroker sps cfg saveTPTP thName nGoal = do
    putStrLn ("running MathServ Broker...")
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg ++ ["[via Broker]"]
    when saveTPTP
        (writeFile (thName++'_':AS_Anno.senName nGoal++".tptp") prob)
    mathServOut <- callMathServ
        MathServCall{mathServService = Broker,
                     mathServOperation = ProblemOpt,
                     problem = prob,
                     proverTimeLimit = tLimit,
                     extraOptions = Nothing}
    msResponse <- parseMathServOut mathServOut
    return (mapMathServResponse msResponse cfg nGoal
                               (prover_name mathServBroker))
    where
      tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg
