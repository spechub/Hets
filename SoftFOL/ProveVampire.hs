{- |
Module      :  $Header$
Description :  Interface to the Vampire theorem prover via MathServe.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Vampire service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SoftFOL.ProveVampire (vampire, vampireCMDLautomaticBatch) where

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
vampire :: Prover Sign Sentence SoftFOLMorphism () ProofTree
vampire = mkAutomaticProver "Vampire" () vampireGUI vampireCMDLautomaticBatch

vampireHelpText :: String
vampireHelpText =
  "No help yet available.\n" ++
  "email hets-devel@informatik.uni-bremen.de " ++
  "for more information.\n"


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
      proverHelpText = vampireHelpText,
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions {problemOutput = ".tptp",
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
           {- ^ theory consisting of a SoftFOL.Sign.Sign
           and a list of Named SoftFOL.Sign.Sentence -}
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
vampireGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName vampire) thName th
                 freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Vampire prover via MathServe.
  Vampire specific functions are omitted by data type ATPFunctions.
-}
vampireCMDLautomaticBatch ::
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
vampireCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName vampire) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  Runs the Vampire service.
-}
runVampire :: SoftFOLProverState
           {- ^ logical part containing the input Sign and axioms and possibly
           goals that have been proved earlier as additional axioms -}
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runVampire sps cfg saveTPTP thName nGoal =
  Exception.catch (do
    prob <- showTPTPProblem thName sps nGoal $ extraOpts cfg ++
                                                 ["Requested prover: Vampire"]
    when saveTPTP
        (writeFile (thName ++ '_' : AS_Anno.senAttr nGoal ++ ".tptp") prob)
    mathServOut <- callMathServ
        MathServCall { mathServService = VampireService,
                      mathServOperation = TPTPProblem,
                      problem = prob,
                      proverTimeLimit = configTimeLimit cfg,
                      extraOptions = Just $ unwords $ extraOpts cfg}
    msResponse <- parseMathServOut mathServOut
    return (mapMathServResponse (getAxioms sps) msResponse cfg nGoal
           $ proverName vampire))
   $ excepToATPResult (proverName vampire) $ AS_Anno.senAttr nGoal
