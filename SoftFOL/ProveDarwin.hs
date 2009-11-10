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
  , darwinGUI
  , darwinCMDLautomatic
  , darwinCMDLautomaticBatch
  , darwinConsChecker
  ) where

-- preliminary hacks for display of CASL models
import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree

import Data.Char (isDigit)
import Data.List (isPrefixOf)
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import System.Cmd
import System.Exit
import System.IO
import System.Process

import GUI.GenericATP
import Interfaces.GenericATPState
import GUI.Utils (infoDialog)
import Proofs.BatchProcessing

-- * Prover implementation

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover.  -}
darwinProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
darwinProver = (mkProverTemplate "Darwin" () darwinGUI)
    { proveCMDLautomatic = Just darwinCMDLautomatic
    , proveCMDLautomaticBatch = Just darwinCMDLautomaticBatch }

darwinConsChecker :: ConsChecker Sign Sentence () SoftFOLMorphism ProofTree
darwinConsChecker = (mkConsChecker "darwin" () consCheck)
  { ccNeedsTimer = False }

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
  , proverHelpText = "no help for darwin available"
  , batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".spass"
      , theoryConfiguration = ".spcf" }
  , runProver = runDarwin
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
darwinGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a SoftFOL.Sign.Sign
           --   and a list of Named SoftFOL.Sign.Sentence
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
darwinGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName darwinProver) thName th
                  freedefs emptyProofTree

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Darwin specific functions are omitted by data type ATPFunctions.
-}
darwinCMDLautomatic ::
           String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
        -> IO (Result.Result ([ProofStatus ProofTree]))
           -- ^ Proof status for goals and lemmas
darwinCMDLautomatic thName defTS th freedefs =
    genericCMDLautomatic (atpFun thName) (proverName darwinProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Darwin prover via MathServe.
  Darwin specific functions are omitted by data type ATPFunctions.
-}
darwinCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
darwinCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName darwinProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions
{- |
  Runs the Darwin service. The tactic script only contains a string for the
  time limit.
-}

consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Sentence SoftFOLMorphism ProofTree
          -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
          -> IO(CCStatus ProofTree)
consCheck thName (TacticScript tl) tm freedefs = case tTarget tm of
    Theory sig nSens -> let
        saveTPTP = False
        proverStateI = spassProverState sig (toNamedList nSens) freedefs
        problem     = showTPTPProblemM thName proverStateI []
        extraOptions  = "-pc true -pmtptp true -fd true -to "
                        ++ tl
        saveFileName  = reverse $ fst $ span (/= '/') $ reverse thName
        runDarwinRealM :: IO(CCStatus ProofTree)
        runDarwinRealM = do
            probl <- problem
            hasProgramm <- system ("which darwin > /dev/null 2> /dev/null")
            case hasProgramm of
              ExitFailure _ -> do
                  infoDialog "Darwin prover" "Darwin not found"
                  return CCStatus
                    { ccResult = Nothing
                    , ccProofTree  = ProofTree "Darwin not found"
                    , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime 0 }
              ExitSuccess -> do
                  when saveTPTP $ writeFile (saveFileName ++ ".tptp") probl
                  t <- getCurrentTime
                  let timeTmpFile = "/tmp/" ++ saveFileName ++ show (utctDay t)
                          ++ "-" ++ show (utctDayTime t) ++ ".tptp"
                  writeFile timeTmpFile probl
                  let command = "darwin " ++ extraOptions ++ " " ++ timeTmpFile
                  (_, outh, errh, proch) <- runInteractiveCommand command
                  (exCode, output, tUsed) <- parseDarwinOut outh errh proch
                  let outState = proofStatM exCode output tUsed
                  return outState
        proofStatM :: ExitCode -> [String] -> Int -> CCStatus ProofTree
        proofStatM exitCode out tUsed = let
             outState = CCStatus
               { ccResult = Just True
               , ccProofTree = ProofTree $ unlines $ show exitCode : out
               , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime
                            $ toInteger tUsed }
             in case exitCode of
                  ExitSuccess -> outState
                  ExitFailure i -> outState
                    { ccResult = if elem i [2, 105, 112]
                        then Nothing else Just False }
        in runDarwinRealM

runDarwin :: SoftFOLProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runDarwin sps cfg saveTPTP thName nGoal = do
  -- putStrLn ("running Darwin...")
  runDarwinReal

  where
    simpleOptions = extraOpts cfg
    extraOptions  = maybe "-pc false"
        ( \ tl -> "-pc false" ++ " -to " ++ show tl) $ timeLimit cfg
    saveFileName  = thName++'_':AS_Anno.senAttr nGoal
    tmpFileName   = (reverse $ fst $ span (/='/') $ reverse thName) ++
                       '_':AS_Anno.senAttr nGoal
    -- tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg

    runDarwinReal = do
      hasProgramm <- system ("which darwin > /dev/null 2> /dev/null")
      case hasProgramm of
        ExitFailure _ -> return
            (ATPError "Could not start Darwin. Is Darwin in your $PATH?",
                  emptyConfig (proverName darwinProver)
                              (AS_Anno.senAttr nGoal) emptyProofTree)
        ExitSuccess -> do
          prob <- showTPTPProblem thName sps nGoal $
                      simpleOptions ++ ["Requested prover: Darwin"]
          when saveTPTP
            (writeFile (saveFileName ++".tptp") prob)
          t <- getCurrentTime
          let timeTmpFile = "/tmp/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".tptp"
          writeFile timeTmpFile prob
          let command = "darwin " ++ extraOptions ++ " " ++ timeTmpFile
          -- putStrLn command
          (_, outh, errh, proch) <- runInteractiveCommand command
          (exCode, output, tUsed) <- parseDarwinOut outh errh proch
          let (err, retval) = proofStat exCode simpleOptions output tUsed
          return (err,
                  cfg{proofStatus = retval,
                      resultOutput = output,
                      timeUsed     = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger tUsed})

    proofStat exitCode options out tUsed =
            case exitCode of
              ExitSuccess -> (ATPSuccess, provedStatus options tUsed)
              ExitFailure 2 -> (ATPError (unlines ("Internal error.":out)),
                                defaultProofStatus options)
              ExitFailure 112 ->
                       (ATPTLimitExceeded, defaultProofStatus options)
              ExitFailure 105 ->
                       (ATPBatchStopped, defaultProofStatus options)
              ExitFailure _ ->
                  (ATPSuccess, disProvedStatus options)

    defaultProofStatus opts =
            (openProofStatus
            (AS_Anno.senAttr nGoal) (proverName darwinProver) $
                                    emptyProofTree)
                       {tacticScript = TacticScript $ show $ ATPTacticScript
                        {tsTimeLimit = configTimeLimit cfg,
                         tsExtraOpts = opts} }

    disProvedStatus opts = (defaultProofStatus opts)
                               {goalStatus = Disproved}

    provedStatus opts ut = ProofStatus
      { goalName = AS_Anno.senAttr nGoal
      , goalStatus = Proved True
      , usedAxioms = getAxioms
      , usedProver = proverName darwinProver
      , proofTree = emptyProofTree
      , usedTime = timeToTimeOfDay $ secondsToDiffTime $ toInteger ut
      , tacticScript = TacticScript $ show $ ATPTacticScript
          { tsTimeLimit = configTimeLimit cfg, tsExtraOpts = opts }}

    getAxioms = let
        fl = formulaLists $ initialLogicalPart sps
        fs = concatMap formulae $ filter isAxiomFormula fl
        in map AS_Anno.senAttr fs

isAxiomFormula :: SPFormulaList -> Bool
isAxiomFormula fl =
    case originType fl of
      SPOriginAxioms -> True
      _              -> False

parseDarwinOut :: Handle        -- ^ handel of stdout
               -> Handle        -- ^ handel of stderr
               -> ProcessHandle -- ^ handel of process
               -> IO (ExitCode, [String], Int)
                       -- ^ (exit code, complete output, used time)
parseDarwinOut outh _ procHndl = do
    --darwin does not write to stderr here, so ignore output
    --err <- hGetLine errh
    --if null err then
  readLineAndParse (ExitFailure 1, [], -1) False
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
          if  "Couldn't find eprover" `isPrefixOf` line
            then do
              waitForProcess procHndl
              return (ExitFailure 2, line : output, to)
            else if "Try darwin -h for further information" `isPrefixOf` line
                  -- error by running darwin.
              then do
                waitForProcess procHndl
                return (ExitFailure 2, line : output, to)
              else if "SZS status" `isPrefixOf` line && not stateFound
                then let state' = words line !! 2 in
                  readLineAndParse (checkSZSState state', line : output, to)
                    True
                else if "CPU  Time" `isPrefixOf` line  -- get cup time
                  then let time = case takeWhile isDigit $ last (words line) of
                             ds@(_ : _) -> read ds
                             _ -> to
                       in readLineAndParse (exCode, line : output, time)
                            stateFound
                  else readLineAndParse (exCode, line : output, to)
                         stateFound
     failure -> do
       waitForProcess procHndl
       return (failure, output, to)

   checkSZSState szsState =
        (\ i -> if i == 0 then ExitSuccess else ExitFailure i) $
        case szsState of
          "Unsolved"         -> 101
          "Open"             -> 102
          "Unknown"          -> 103
          "Assumed"          -> 104
          "Stopped"          -> 105
          "Error"            -> 106
          "InputError"       -> 107
          "OSError"          -> 108
          "Forced"           -> 109
          "User"             -> 110
          "ResourceOut"      -> 111
          "Timeout"          -> 112
          "MemoryOut"        -> 113
          "Gaveup"           -> 114
          "Incomplete"       -> 115
          "Inappropriate"    -> 116
          "NotTested"        -> 117
          "NotTestedYet"     -> 118
          "CounterSatisfiable" -> 119
          "CounterTheorem"   -> 120
          "CounterEquivalent" -> 121
          "WeakerCounterTheorem" -> 122
          "UnsatisfiableConclusion" -> 123
          "EquivalentCounterTheorem" -> 124
          "Unsatisfiable"    -> 125
          "SatisfiableCounterConclusionContradictoryAxioms" -> 126
          "UnsatisfiableConclusionContradictoryAxioms" -> 127
          "NoConsequence"    -> 128
          "CounterSatisfiabilityPreserving" -> 129
          "CounterSatisfiabilityPartialMapping" -> 130
          "CounterSatisfiabilityMapping" -> 131
          "CounterSatisfiabilityBijection" -> 132
          _ -> 0

    -- check if darwin running
   isProcessRun = do
      exitcode <- getProcessExitCode procHndl
      case exitcode of
        Nothing -> return ExitSuccess
        Just (ExitFailure i) -> return (ExitFailure i)
        Just ExitSuccess     -> return ExitSuccess
