{- |
Module      :  $Header$
Description :  Interface to the Leo-II theorem prover.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Prover)

LEO-II theorem prover for THF0
-}

module THF.ProveLeoII where

import Logic.Prover

import THF.Cons
import THF.Sign
import THF.ProverState

import Common.AS_Annotation as AS_Anno
import Common.Result
import Common.ProofTree
import Common.Utils (basename, getTempFile, timeoutCommand)
import Common.SZSOntology

import GUI.GenericATP

import Interfaces.GenericATPState

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Proofs.BatchProcessing

import System.Directory

import Data.List
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (picosecondsToDiffTime, secondsToDiffTime)

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

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> ATPFunctions SignTHF SentenceTHF MorphismTHF ProofTree ProverStateTHF
atpFun _ = ATPFunctions
  { initialProverState = initialProverStateTHF
  , atpTransSenName = id
  , atpInsertSentence = insertSentenceTHF
  , goalOutput = showProblemTHF
  , proverHelpText = leoIIHelpText
  , batchTimeEnv = "HETS_LEOII_BATCH_TIME_LIMIT"
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
    -> GenericConfig ProofTree -- ^ configuration to use
    -> Bool -- ^ True means save THF file
    -> String -- ^ name of the theory in the DevGraph
    -> Named SentenceTHF -- ^ goal to prove
    -> IO (ATPRetval, GenericConfig ProofTree)
    -- ^ (retval, configuration with proof status and complete output)
runLeoII pst cfg saveTHF thName nGoal = do
    let options = extraOpts cfg
        tout = maybe leoIITimeout (+ 1) (timeLimit cfg)
        extraOptions = maybe "-po 1" (("-po 1 -t " ++) . show) (timeLimit cfg)
        tmpFileName = thName ++ '_' : AS_Anno.senAttr nGoal
    prob <- showProblemTHF pst nGoal []
    runRes <- runLeoIIProcess tout saveTHF extraOptions tmpFileName prob
    case runRes of
        Nothing ->
            let ctime = timeToTimeOfDay $ secondsToDiffTime
                            $ toInteger leoIITimeout
            in return (ATPTLimitExceeded, cfg
                        { proofStatus =
                            (openProofStatus (AS_Anno.senAttr nGoal)
                                            "LEO-II" emptyProofTree)
                                { usedTime = ctime
                                , tacticScript = TacticScript
                                    $ show ATPTacticScript
                                        { tsTimeLimit = configTimeLimit cfg
                                        , tsExtraOpts = options} }
                        , timeUsed = ctime })
        Just (exitCode, out, tUsed) ->
         let ctime = timeToTimeOfDay $ picosecondsToDiffTime
                        $ toInteger $ tUsed * 1000000000
             (err, retval) = case () of
                _ | szsProved exitCode      -> (ATPSuccess, provedStatus)
                _ | szsDisproved exitCode   -> (ATPSuccess, disProvedStatus)
                _ | szsTimeout exitCode     ->
                                    (ATPTLimitExceeded, defaultProofStatus)
                _ | szsStopped exitCode   ->
                                    (ATPBatchStopped, defaultProofStatus)
                _                         ->
                                    (ATPError exitCode, defaultProofStatus)
             defaultProofStatus =
              (openProofStatus (AS_Anno.senAttr nGoal) "LEO-II" emptyProofTree)
                       { usedTime = ctime
                       , tacticScript = TacticScript $ show ATPTacticScript
                            { tsTimeLimit = configTimeLimit cfg
                            , tsExtraOpts = options} }
             disProvedStatus = defaultProofStatus {goalStatus = Disproved}
             provedStatus = defaultProofStatus { goalStatus = Proved True
                                              , usedAxioms = getAxioms pst }
         in return (err, cfg { proofStatus = retval
                         , resultOutput = out
                         , timeUsed = ctime })

-- Run the Leo-II process. timeoutCommand is used to terminate leo if it does
-- not terminate itself after the timeout time is over.
runLeoIIProcess
    :: Int -- ^ timeout time in seconds
    -> Bool -- ^ save problem
    -> String -- ^ options
    -> String -- ^ filename without extension
    -> String -- ^ problem
    -> IO (Maybe (String, [String], Int))
runLeoIIProcess tout saveTHF options tmpFileName prob = do
    let tmpFile = basename tmpFileName ++ ".thf"
    when saveTHF (writeFile tmpFile prob)
    timeTmpFile <- getTempFile prob tmpFile
    mres <- timeoutCommand tout "leo" (words options ++ [timeTmpFile])
    maybe (return Nothing) (\ (_, pout, _) -> do
        let l = lines pout
            (res, _, tUsed) = parseOutput l
        removeFile timeTmpFile
        return $ Just (res, l, tUsed)) mres

-- parse the output and return the szsStatus and the used time.
parseOutput :: [String] -> (String, Bool, Int)
  -- ^ (exit code, status found, used time ins ms)
parseOutput = foldl checkLine ("", False, -1) where
   checkLine (exCode, stateFound, to) line = case getSZSStatusWord line of
        Just szsState | not stateFound -> (szsState, True, to)
        _ -> case words (fromMaybe "" $ stripPrefix "# Total time" line) of
            _ : (tim : _) -> -- ":" : (tim : ("s" : []))
                let time = round $ (read tim :: Float) * 1000
                in (exCode, stateFound, time)
            _ -> (exCode, stateFound, to)

-- try to read the szs status from a given String
getSZSStatusWord :: String -> Maybe String
getSZSStatusWord line =
    case words (fromMaybe "" $ stripPrefix "% SZS status" line) of
        [] -> Nothing
        w : _ -> Just w

-- the standart leo-II timeout time
leoIITimeout :: Int
leoIITimeout = 601
