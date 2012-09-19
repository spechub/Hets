{- |
Module      :  $Header$
Description :  Interface to the Leo-II theorem prover.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Prover)

Isabelle theorem prover for THF
-}

module THF.ProveIsabelle where

import Logic.Prover

import THF.Cons
import THF.Sign
import THF.ProverState

import Common.AS_Annotation as AS_Anno
import Common.Result
import Common.ProofTree
import Common.Utils (basename, timeoutCommand)
import Common.SZSOntology

import GUI.GenericATP

import Interfaces.GenericATPState

import Control.Monad (unless)
import qualified Control.Concurrent as Concurrent

import Proofs.BatchProcessing

import System.Directory

import Data.List
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)

{- | The Prover implementation. First runs the batch prover (with
  graphical feedback), then starts the GUI prover. -}
isaName :: String
isaName = "Isabelle (automated)"

isaHelp :: String
isaHelp = "Help"

isaTool :: String
isaTool = "tptp_isabelle_demo"

isaProver :: Prover SignTHF SentenceTHF MorphismTHF () ProofTree
isaProver = mkAutomaticProver isaName ()
 (isaGUI isaHelp isaName isaTool) (isaCMDLautomaticBatch isaName isaHelp isaTool)

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> String -- help text
  -> String -- tool
  -> ATPFunctions SignTHF SentenceTHF MorphismTHF ProofTree ProverStateTHF
atpFun _ hlp tool = ATPFunctions
  { initialProverState = initialProverStateTHF
  , atpTransSenName = id
  , atpInsertSentence = insertSentenceTHF
  , goalOutput = showProblemTHF
  , proverHelpText = hlp
  , batchTimeEnv = "HETS_ISA_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions { 
      problemOutput = ".p"
    , proverOutput = ""
    , theoryConfiguration = "" }
  , runProver = runIsa tool
  , createProverOptions = extraOpts }

-- ** GUI

{- |
  Invokes the generic prover GUI. Isabelle specific functions are omitted by
  data type ATPFunctions.
-}
isaGUI :: String -- help text
    -> String -- name
    -> String -- tool
    -> String -- ^ theory name
    -> Theory SignTHF SentenceTHF ProofTree
    -> [FreeDefMorphism SentenceTHF MorphismTHF] -- ^ freeness constraints
    -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
isaGUI hlp name tool thName th freedefs =
    genericATPgui (atpFun thName hlp tool) True name thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Isabelle prover.
  Isabelle specific functions are omitted by data type ATPFunctions.
-}
isaCMDLautomaticBatch
  :: String -- name
  -> String -- help
  -> String -- tool
  -> Bool -- ^ True means include proved theorems
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
isaCMDLautomaticBatch name hlp tool inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName hlp tool) inclProvedThs saveProblem_batch
        resultMVar name thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
   Runs the Leo-II prover.
-}
runIsa :: String -- tool
    -> ProverStateTHF
    -> GenericConfig ProofTree -- ^ configuration to use
    -> Bool -- ^ True means save THF file
    -> String -- ^ name of the theory in the DevGraph
    -> Named SentenceTHF -- ^ goal to prove
    -> IO (ATPRetval, GenericConfig ProofTree)
    -- ^ (retval, configuration with proof status and complete output)
runIsa tool pst cfg saveTHF thName nGoal = do
    let tout = maybe 20 (+ 10) (timeLimit cfg)
        tmpFileName = thName ++ '_' : AS_Anno.senAttr nGoal
    prob <- showProblemTHF pst nGoal []
    runRes <- runIsaProcess tool tout saveTHF tmpFileName prob
    case runRes of
        Nothing -> return (ATPTLimitExceeded, cfg
                        { proofStatus =
                            (openProofStatus (AS_Anno.senAttr nGoal)
                                            "Isa" emptyProofTree)
                                { usedTime =
                                   timeToTimeOfDay $ secondsToDiffTime $
                                   toInteger tout
                                , tacticScript = TacticScript
                                    $ show ATPTacticScript
                                        { tsTimeLimit = configTimeLimit cfg,
                                          tsExtraOpts = [] } }
                        , timeUsed = 
                           timeToTimeOfDay $ secondsToDiffTime $
                           toInteger tout })
        Just (exitCode, out, tUsed) ->
         let (err, retval) = case () of
                _ | szsProved exitCode      -> (ATPSuccess, provedStatus)
                _ | szsDisproved exitCode   -> (ATPSuccess, disProvedStatus)
                _ | szsTimeout exitCode     ->
                                    (ATPTLimitExceeded, defaultProofStatus)
                _ | szsStopped exitCode   ->
                                    (ATPBatchStopped, defaultProofStatus)
                _                         ->
                                    (ATPError exitCode, defaultProofStatus)
             defaultProofStatus =
              (openProofStatus (AS_Anno.senAttr nGoal) "Isabelle" emptyProofTree)
                       { usedTime =
                          timeToTimeOfDay $ secondsToDiffTime $
                          toInteger tUsed
                       , tacticScript = TacticScript $ show ATPTacticScript
                            { tsTimeLimit = configTimeLimit cfg,
                              tsExtraOpts = [] } }
             disProvedStatus = defaultProofStatus {goalStatus = Disproved}
             provedStatus = defaultProofStatus { goalStatus = Proved True
                                              , usedAxioms = getAxioms pst }
         in return (err, cfg { proofStatus = retval
                         , resultOutput = out
                         , timeUsed = 
                             timeToTimeOfDay $ secondsToDiffTime $
                             toInteger tUsed })

-- Run the Isabelle process. timeoutCommand is used to terminate Isabelle if it does
-- not terminate itself after the timeout time is over.
runIsaProcess
    :: String -- tool
    -> Int -- ^ timeout time in seconds
    -> Bool -- ^ save problem
    -> String -- ^ filename without extension
    -> String -- ^ problem
    -> IO (Maybe (String, [String], Int))
runIsaProcess tool tout saveTHF tmpFileName prob = do
    let tmpFile = basename tmpFileName ++ ".p"
    writeFile tmpFile prob
    mres <- timeoutCommand tout "time" ["isabelle", tool, show (tout-10), tmpFile]
    maybe (return Nothing) (\ (_, pout, _) -> do
        let l = lines pout
            (res', _, tUsed) = parseOutput l
            res = if null res' then concat $ filter (isPrefixOf "*** ") l
                  else res'
        unless saveTHF $ removeFile tmpFile
        return $ Just (res, l, tUsed)) mres

-- parse the output and return the szsStatus and the used time.
parseOutput :: [String] -> (String, Bool, Int)
  -- ^ (exit code, status found, used time ins ms)
parseOutput = foldl checkLine ("", False, -1) where
   checkLine (exCode, stateFound, to) line = case getSZSStatusWord line of
        Just szsState | not stateFound -> (szsState, True, to)
        _ -> case (fromMaybe "" $ stripPrefix "real\t" line) of
            [] -> (exCode, stateFound, to)
            s -> let (m:secs:_) = sp (=='m') s
                 in (exCode, stateFound, (read m)*60 + (read secs))
                 where sp p str = case dropWhile p str of
                                     "" -> []
                                     s' -> w : sp p s''
                                      where (w,s'') = break p s'

-- try to read the szs status from a given String
getSZSStatusWord :: String -> Maybe String
getSZSStatusWord line =
    case words (fromMaybe "" $ stripPrefix "% SZS status" line) of
        [] -> Nothing
        w : _ -> Just w
