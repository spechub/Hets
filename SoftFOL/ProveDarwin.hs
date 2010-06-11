{- |
Module      :  $Header$
Description :  Interface to the TPTP theorem prover via Darwin.
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Darwin service, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS, and
<http://combination.cs.uiowa.edu/Darwin/> for Darwin.
-}

module SoftFOL.ProveDarwin
  ( darwinProver
  , darwinCMDLautomaticBatch
  , darwinConsChecker
  , ProverBinary (..)
  ) where

-- preliminary hacks for display of CASL models
import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree
import Common.ProverTools
import Common.SZSOntology

import Data.Char (isDigit)
import Data.List
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime (..), secondsToDiffTime, getCurrentTime)

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import System.Exit
import System.IO
import System.Process

import GUI.GenericATP
import Interfaces.GenericATPState
import Proofs.BatchProcessing

-- * Prover implementation

data ProverBinary = Darwin | EDarwin

proverBinary :: ProverBinary -> String
proverBinary b = case b of
  Darwin -> "darwin"
  EDarwin -> "e-darwin"

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover. -}
darwinProver
  :: ProverBinary -> Prover Sign Sentence SoftFOLMorphism () ProofTree
darwinProver b = mkAutomaticProver (proverBinary b) () (darwinGUI b)
  $ darwinCMDLautomaticBatchAux b

darwinConsChecker
  :: ProverBinary -> ConsChecker Sign Sentence () SoftFOLMorphism ProofTree
darwinConsChecker b = (mkConsChecker (proverBinary b) () $ consCheck b)
  { ccNeedsTimer = False }

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: ProverBinary  -- ^ the actual binary
  -> String -- ^ theory name
  -> ATPFunctions Sign Sentence SoftFOLMorphism ProofTree SoftFOLProverState
atpFun b thName = ATPFunctions
  { initialProverState = spassProverState
  , atpTransSenName = transSenName
  , atpInsertSentence = insertSentenceGen
  , goalOutput = showTPTPProblem thName
  , proverHelpText = "no help for darwin available"
  , batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".spass"
      , theoryConfiguration = ".spcf" }
  , runProver = runDarwin b
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
darwinGUI
  :: ProverBinary -- ^ the actual binary
  -> String -- ^ theory name
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
darwinGUI b thName th freedefs =
    genericATPgui (atpFun b thName) True (proverBinary b) thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Darwin prover.
  Darwin specific functions are omitted by data type ATPFunctions.
-}
darwinCMDLautomaticBatch
  :: Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     -- ^ fst: identifier of the batch thread for killing it
     -- snd: MVar to wait for the end of the thread
darwinCMDLautomaticBatch = darwinCMDLautomaticBatchAux Darwin

darwinCMDLautomaticBatchAux
  :: ProverBinary -- ^ the actual binary
  -> Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory Sign Sentence ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     -- ^ fst: identifier of the batch thread for killing it
     -- snd: MVar to wait for the end of the thread
darwinCMDLautomaticBatchAux b inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun b thName) inclProvedThs saveProblem_batch
        resultMVar (proverBinary b) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions
{- |
  Runs the Darwin service. The tactic script only contains a string for the
  time limit.
-}

consCheck
  :: ProverBinary
  -> String
  -> TacticScript
  -> TheoryMorphism Sign Sentence SoftFOLMorphism ProofTree
  -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
  -> IO (CCStatus ProofTree)
consCheck b thName (TacticScript tl) tm freedefs = case tTarget tm of
    Theory sig nSens -> let
        saveTPTP = False
        proverStateI = spassProverState sig (toNamedList nSens) freedefs
        problem = showTPTPProblemM thName proverStateI []
        extraOptions =
          "-pc false -pmtptp true -fd true -to " ++ tl
        saveFileName = reverse $ fst $ span (/= '/') $ reverse thName
        runDarwinRealM :: IO (CCStatus ProofTree)
        runDarwinRealM = do
            let bin = proverBinary b
            probl <- problem
            noProg <- missingExecutableInPath bin
            if noProg then
                  return CCStatus
                    { ccResult = Nothing
                    , ccProofTree = ProofTree "Darwin not found"
                    , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime 0 }
              else do
                  when saveTPTP $ writeFile (saveFileName ++ ".tptp") probl
                  t <- getCurrentTime
                  let timeTmpFile = "/tmp/" ++ saveFileName ++ show (utctDay t)
                          ++ "-" ++ show (utctDayTime t) ++ ".tptp"
                  writeFile timeTmpFile probl
                  let command = bin ++ " " ++ extraOptions ++ " " ++ timeTmpFile
                  (_, outh, errh, proch) <- runInteractiveCommand command
                  (szsState, output, tUsed) <- parseDarwinOut outh errh proch
                  let outState = proofStatM szsState output tUsed
                  return outState
        proofStatM :: String -> [String] -> Int -> CCStatus ProofTree
        proofStatM exitCode out tUsed = let
             outState = CCStatus
               { ccResult = Just True
               , ccProofTree = ProofTree $ unlines $ exitCode : out
               , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime
                            $ toInteger tUsed }
             in if szsProved exitCode then outState else
                    outState
                    { ccResult = if szsDisproved exitCode then Just False
                                 else Nothing }
        in runDarwinRealM

runDarwin
  :: ProverBinary
  -> SoftFOLProverState
  -- ^ logical part containing the input Sign and axioms and possibly
  -- goals that have been proved earlier as additional axioms
  -> GenericConfig ProofTree -- ^ configuration to use
  -> Bool -- ^ True means save TPTP file
  -> String -- ^ name of the theory in the DevGraph
  -> AS_Anno.Named SPTerm -- ^ goal to prove
  -> IO (ATPRetval, GenericConfig ProofTree)
     -- ^ (retval, configuration with proof status and complete output)
runDarwin b sps cfg saveTPTP thName nGoal = runDarwinReal where
    bin = proverBinary b
    simpleOptions = extraOpts cfg
    extraOptions = maybe "-pc false"
             (("-pc false -to " ++) . show) (timeLimit cfg)
    saveFileName = thName ++ '_' : AS_Anno.senAttr nGoal
    tmpFileName = reverse (fst $ span (/= '/') $ reverse thName) ++
                       '_' : AS_Anno.senAttr nGoal
    runDarwinReal = do
      noProg <- missingExecutableInPath bin
      if noProg then
        return
            (ATPError ("Could not start " ++ bin ++ ". Check your $PATH"),
                  emptyConfig bin
                              (AS_Anno.senAttr nGoal) emptyProofTree)
        else do
          prob <- showTPTPProblem thName sps nGoal $
                      simpleOptions ++ ["Requested prover: " ++ bin]
          when saveTPTP
            (writeFile (saveFileName ++ ".tptp") prob)
          t <- getCurrentTime
          let timeTmpFile = "/tmp/" ++ tmpFileName ++ show (utctDay t) ++
                               "-" ++ show (utctDayTime t) ++ ".tptp"
          writeFile timeTmpFile prob
          let command = bin ++ " " ++ extraOptions ++ " " ++ timeTmpFile
          (_, outh, errh, proch) <- runInteractiveCommand command
          (exCode, output, tUsed) <- parseDarwinOut outh errh proch
          let (err, retval) = proofStat exCode simpleOptions output tUsed
          return (err,
                  cfg {proofStatus = retval,
                      resultOutput = output,
                      timeUsed = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger tUsed})

    proofStat exitCode options out tUsed = case () of
        _ | szsProved exitCode -> (ATPSuccess, provedStatus options tUsed)
        _ | szsDisproved exitCode -> (ATPSuccess, disProvedStatus options)
        _ | szsTimeout exitCode ->
              (ATPTLimitExceeded, defaultProofStatus options)
        _ | szsStopped exitCode ->
              (ATPBatchStopped, defaultProofStatus options)
        _ -> (ATPError (unlines (exitCode : out)),
                                defaultProofStatus options)
    defaultProofStatus opts =
            (openProofStatus
            (AS_Anno.senAttr nGoal) bin emptyProofTree)
                       {tacticScript = TacticScript $ show ATPTacticScript
                        {tsTimeLimit = configTimeLimit cfg,
                         tsExtraOpts = opts} }

    disProvedStatus opts = (defaultProofStatus opts)
                               {goalStatus = Disproved}

    provedStatus opts ut = ProofStatus
      { goalName = AS_Anno.senAttr nGoal
      , goalStatus = Proved True
      , usedAxioms = getAxioms
      , usedProver = bin
      , proofTree = emptyProofTree
      , usedTime = timeToTimeOfDay $ secondsToDiffTime $ toInteger ut
      , tacticScript = TacticScript $ show ATPTacticScript
          { tsTimeLimit = configTimeLimit cfg, tsExtraOpts = opts }}

    getAxioms = let
        fl = formulaLists $ initialLogicalPart sps
        fs = concatMap formulae $ filter isAxiomFormula fl
        in map AS_Anno.senAttr fs

isAxiomFormula :: SPFormulaList -> Bool
isAxiomFormula fl =
    case originType fl of
      SPOriginAxioms -> True
      _ -> False

getSZSStatusWord :: String -> Maybe String
getSZSStatusWord line = case words
    $ fromMaybe (fromMaybe "" $ stripPrefix "% SZS status" line)
    $ stripPrefix "SZS status" line of
  [] -> Nothing
  w : _ -> Just w

parseDarwinOut :: Handle        -- ^ handel of stdout
               -> Handle        -- ^ handel of stderr
               -> ProcessHandle -- ^ handel of process
               -> IO (String, [String], Int)
                       -- ^ (exit code, complete output, used time)
parseDarwinOut outh _ procHndl =
    -- darwin does not write to stderr here, so ignore output
    -- err <- hGetLine errh
    -- if null err then
  readLineAndParse ("", [], -1) False
  where
   readLineAndParse (exCode, output, to) stateFound = do
    procState <- isProcessRun
    case procState of
     ExitSuccess -> do
      iseof <- hIsEOF outh
      if iseof then
          do -- ec <- isProcessRun proc
             waitForProcess procHndl
             return (exCode, reverse output, to)
        else do
          line <- hGetLine outh
          if isPrefixOf "Couldn't find eprover" line
             || isInfixOf "darwin -h for further information" line
                -- error by running darwin.
            then do
              waitForProcess procHndl
              return ("Internal error.", line : output, to)
            else case getSZSStatusWord line of
                Just szsState | not stateFound ->
                  readLineAndParse (szsState, line : output, to)
                    True
                _ -> if "CPU  Time" `isPrefixOf` line  -- get cup time
                  then let time = case takeWhile isDigit $ last (words line) of
                             ds@(_ : _) -> read ds
                             _ -> to
                       in readLineAndParse (exCode, line : output, time)
                            stateFound
                  else readLineAndParse (exCode, line : output, to)
                         stateFound
     ExitFailure failure -> do
       waitForProcess procHndl
       return ("Process error " ++ show failure, output, to)

    -- check if darwin running
   isProcessRun = do
      exitcode <- getProcessExitCode procHndl
      case exitcode of
        Nothing -> return ExitSuccess
        Just (ExitFailure i) -> return (ExitFailure i)
        Just ExitSuccess -> return ExitSuccess
