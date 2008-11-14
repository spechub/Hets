{- |
Module      :  $Header$
Description :  Interface to the Vampire theorem prover via MathServe.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Vampire service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SoftFOL.ProveVampire (vampire,vampireGUI,vampireCMDLautomatic,
                           vampireCMDLautomaticBatch) where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.MathServMapping
import SoftFOL.MathServParsing
import SoftFOL.ProverState

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree

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
vampire :: Prover Sign Sentence SoftFOLMorphism () ProofTree
vampire = (mkProverTemplate "Vampire" () vampireGUI)
    { proveCMDLautomatic = Just vampireCMDLautomatic
    , proveCMDLautomaticBatch = Just vampireCMDLautomaticBatch }

vampireHelpText :: String
vampireHelpText =
  "No help yet available.\n" ++
  "Ask Dominik L\252cke (luecke@informatik.uni-bremen.de) " ++
  "for more information.\n"


-- * Main prover functions

-- ** Utility functions

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Sentence ProofTree SoftFOLProverState
atpFun thName = ATPFunctions
    { initialProverState = spassProverState,
      atpTransSenName = transSenName,
      atpInsertSentence = insertSentenceGen,
      goalOutput = showTPTPProblem thName,
      proverHelpText = vampireHelpText,
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".tptp",
                                      proverOutput = ".vamp",
                                      theoryConfiguration = ".spcf"},
      runProver = runVampire,
      createProverOptions = extraOpts}

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
vampireGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a SoftFOL.Sign.Sign
           --   and a list of Named SoftFOL.Sign.Sentence
           -> IO([Proof_status ProofTree]) -- ^ proof status for each goal
vampireGUI thName th =
    genericATPgui (atpFun thName) True (prover_name vampire) thName th $
                  emptyProofTree

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Vampire specific functions are omitted by data type ATPFunctions.
-}
vampireCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status ProofTree]))
           -- ^ Proof status for goals and lemmas
vampireCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name vampire) thName
        (parseTactic_script batchTimeLimit [] defTS) th emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Vampire prover via MathServe.
  Vampire specific functions are omitted by data type ATPFunctions.
-}
vampireCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
vampireCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name vampire) thName
        (parseTactic_script batchTimeLimit [] defTS) th emptyProofTree

{- |
  Runs the Vampire service.
-}
runVampire :: SoftFOLProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runVampire sps cfg saveTPTP thName nGoal = do
--    putStrLn ("running MathServ VampireService...")
  Exception.catch (do
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg ++
                                                 ["Requested prover: Vampire"]
    when saveTPTP
        (writeFile (thName++'_':AS_Anno.senAttr nGoal++".tptp") prob)
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
