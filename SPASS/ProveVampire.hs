{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover using Vampire.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Vampire service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SPASS.ProveVampire (vampire,vampireGUI,vampireCMDLautomatic,
                           vampireCMDLautomaticBatch) where

import Logic.Prover

import SPASS.Sign
import SPASS.Translate
import SPASS.MathServMapping
import SPASS.MathServParsing
import SPASS.ProverState

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
vampire :: Prover Sign Sentence ATP_ProofTree
vampire = emptyProverTemplate
         { prover_name = "Vampire",
           prover_sublogic = "SoftFOL",
           proveGUI = Just vampireGUI,
           proveCMDLautomatic = Just vampireCMDLautomatic,
           proveCMDLautomaticBatch = Just vampireCMDLautomaticBatch
         }

spassHelpText :: String
spassHelpText =
  "No help yet available.\n" ++
  "Ask Klaus L\252ttich (luettich@informatik.uni-bremen.de) " ++
  "for more information.\n"


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
      runProver = runVampire,
      createProverOptions = extraOpts}

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
vampireGUI :: String -- ^ theory name
           -> Theory Sign Sentence ATP_ProofTree
           -- ^ theory consisting of a SPASS.Sign.Sign
           --   and a list of Named SPASS.Sign.Sentence
           -> IO([Proof_status ATP_ProofTree]) -- ^ proof status for each goal
vampireGUI thName th =
    genericATPgui (atpFun thName) True (prover_name vampire) thName th $
                  ATP_ProofTree ""

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Vampire specific functions are omitted by data type ATPFunctions.
-}
vampireCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status ATP_ProofTree]))
           -- ^ Proof status for goals and lemmas
vampireCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name vampire) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the SPASS prover.
  Vampire specific functions are omitted by data type ATPFunctions.
-}
vampireCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ATP_ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree -- ^ theory consisting of a
           --   'SPASS.Sign.Sign' and a list of Named 'SPASS.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
vampireCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name vampire) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

{- |
  Runs the Vampire service.
-}
runVampire :: SPASSProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ATP_ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ATP_ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runVampire sps cfg saveTPTP thName nGoal = do
--    putStrLn ("running MathServ VampireService...")
  Exception.catch (do
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg ++
                                                 ["Requested prover: Vampire"]
    when saveTPTP
        (writeFile (thName++'_':AS_Anno.senName nGoal++".tptp") prob)
    mathServOut <- callMathServ
        MathServCall{ mathServService = VampireService,
                      mathServOperation = TPTPProblem,
                      problem = prob,
                      proverTimeLimit = tLimit,
                      extraOptions = Just $ unwords $ extraOpts cfg}
    msResponse <- parseMathServOut mathServOut
    return (mapMathServResponse msResponse cfg nGoal $ prover_name vampire))
    (excepToATPResult (prover_name vampire) nGoal)
  where
    tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg
