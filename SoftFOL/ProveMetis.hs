{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (ATP GUI)

call metis prover
-}

module SoftFOL.ProveMetis
  ( metisProver
  , metisProveCMDLautomaticBatch
  ) where

import Common.AS_Annotation as AS_Anno
import Common.ProofTree
import Common.Timing
import Common.Utils
import Common.SZSOntology
import qualified Common.Result as Result

import qualified Control.Concurrent as Concurrent
import Control.Monad

import Data.List
import Data.Maybe

import GUI.GenericATP

import Interfaces.GenericATPState

import Logic.Prover

import Proofs.BatchProcessing

import SoftFOL.ProverState
import SoftFOL.Sign
import SoftFOL.Translate

import System.Directory
import System.Exit
import System.IO

-- | The Prover implementation.
metisProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
metisProver = mkAutomaticProver "metis" () metisGUI
  metisProveCMDLautomaticBatch

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> ATPFunctions Sign Sentence SoftFOLMorphism ProofTree SoftFOLProverState
atpFun thName = ATPFunctions
  { initialProverState = spassProverState
  , atpTransSenName = transSenName
  , atpInsertSentence = insertSentenceGen
  , goalOutput = showTPTPProblem thName
  , proverHelpText = ""
  , batchTimeEnv = ""
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".spass"
      , theoryConfiguration = "" }
  , runProver = runMetis
  , createProverOptions = extraOpts }


{- |
  Invokes the generic prover GUI.
-}
metisGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           {- ^ theory consisting of a SoftFOL.Sign.Sign
           and a list of Named SoftFOL.Sign.Sentence -}
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
metisGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName metisProver) thName th
                  freedefs emptyProofTree


-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Metis prover.
-}

metisProveCMDLautomaticBatch ::
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
metisProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName metisProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree


runMetis :: SoftFOLProverState
           {- ^ logical part containing the input Sign and axioms and possibly
           goals that have been proved earlier as additional axioms -}
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runMetis sps cfg saveTPTP thName nGoal = do
  let
        saveFile = thName ++ '_' : AS_Anno.senAttr nGoal
        myTimeLimit = configTimeLimit cfg

  prob <- showTPTPProblem thName sps nGoal []
  when saveTPTP
      (writeFile (saveFile ++ ".tptp") prob)
  tmppath <- getTemporaryDirectory
  (timeTmpFile, temphandel) <- openTempFile tmppath "tmp.tptp"
  hPutStr temphandel prob
  hClose temphandel
  start <- getHetsTime
  end <- timeoutCommand myTimeLimit "metis" (extraOpts cfg ++ [timeTmpFile])
  finish <- getHetsTime
  let executetime = diffHetsTime finish start
      newCfg = cfg
        { timeUsed = executetime
        , proofStatus = (proofStatus cfg) {usedTime = executetime}}
  removeFile timeTmpFile
  return $ case end of
    Nothing ->
      ( ATPTLimitExceeded
      , newCfg
        { timeLimitExceeded = True
        , resultOutput = ["TimeOut"] })
    Just (ex, out, err) ->
      let finCfg = newCfg { resultOutput = lines $ out ++ err }
      in case ex of
         ExitSuccess ->
           ( ATPSuccess
           , finCfg
             { proofStatus = (proofStatus finCfg)
               { usedAxioms = getAxioms sps
               , goalStatus = getGoalStatus out }})
         _ -> (ATPError err, finCfg)

{-
  mapping from SZS Status to Goalstatus
-}
getGoalStatus :: String -> GoalStatus
getGoalStatus l = let ll = lines l in
  case mapMaybe (stripPrefix "SZS status") ll of
  [] -> Open (Reason ll)
  z@(s : _) -> case words s of
    w : _
      | szsProved w -> Proved True
      | szsDisproved w -> Disproved
    _ -> Open (Reason z)

{-
  from ProveDarwin.hs
-}
getAxioms :: SoftFOLProverState -> [String]
getAxioms = map AS_Anno.senAttr . concatMap formulae . filter isAxiomFormula
   . formulaLists . initialLogicalPart

isAxiomFormula :: SPFormulaList -> Bool
isAxiomFormula fl =
    case originType fl of
      SPOriginAxioms -> True
      _ -> False
