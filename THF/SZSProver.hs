{- |
Module      :  ./THF/SZSProver.hs
Description :  General Interface to a prover using SZS status messages
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Prover)

Isabelle theorem prover for THF
-}

module THF.SZSProver
  ( createSZSProver
  , ProverType
  , ProverFuncs (..)
  ) where

import Logic.Prover

import THF.As (THFFormula)
import THF.Sign
import THF.ProverState
import THF.Sublogic

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


data ProverFuncs = ProverFuncs {
 cfgTimeout :: GenericConfig ProofTree -> Int, -- in seconds
 proverCommand :: Int -> String -> GenericConfig ProofTree ->
                  IO (String, [String]),
 -- timeout -> problem file
 getMessage :: String -> String -> String -> String,
 -- result -> std out -> std err
 getTimeUsed :: String -> Maybe Int -- in seconds
}

type ProverType = Prover SignTHF THFFormula MorphismTHF THFSl ProofTree

createSZSProver :: String -> String -> String -> ProverFuncs ->
                   ProverType
createSZSProver bin name hlp d = mkAutomaticProver bin name tHF0
 (proverGUI hlp name d)
 (proverCMDLautomaticBatch hlp name d)

atpFun :: ProverFuncs
  -> String -- name
  -> String -- ^ theory name
  -> String -- help text
  -> ATPFunctions SignTHF THFFormula MorphismTHF ProofTree ProverStateTHF
atpFun d name _ hlp = ATPFunctions
  { initialProverState = initialProverStateTHF
  , atpTransSenName = id
  , atpInsertSentence = insertSentenceTHF
  , goalOutput = showProblemTHF
  , proverHelpText = hlp
  , batchTimeEnv = "HETS_TPTP_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions {
      problemOutput = ".p"
    , proverOutput = ""
    , theoryConfiguration = "" }
  , runProver = runProverT d name
  , createProverOptions = extraOpts }

proverGUI :: String -- help text
    -> String -- name
    -> ProverFuncs
    -> String -- ^ theory name
    -> Theory SignTHF THFFormula ProofTree
    -> [FreeDefMorphism THFFormula MorphismTHF] -- ^ freeness constraints
    -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
proverGUI hlp name d thName th freedefs =
    genericATPgui (atpFun d name thName hlp) True name thName th
                  freedefs emptyProofTree

proverCMDLautomaticBatch
  :: String -- help
  -> String -- name
  -> ProverFuncs
  -> Bool -- ^ True means include proved theorems
  -> Bool -- ^ True means save problem file
  -> Concurrent.MVar (Result [ProofStatus ProofTree])
  -- ^ used to store the result of the batch run
  -> String -- ^ theory name
  -> TacticScript -- ^ default tactic script
  -> Theory SignTHF THFFormula ProofTree
  -- ^ theory consisting of a signature and sentences
  -> [FreeDefMorphism THFFormula MorphismTHF] -- ^ freeness constraints
  -> IO (Concurrent.ThreadId, Concurrent.MVar ())
     {- ^ fst: identifier of the batch thread for killing it
     snd: MVar to wait for the end of the thread -}
proverCMDLautomaticBatch hlp name d inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun d name thName hlp) inclProvedThs
        saveProblem_batch
        resultMVar name thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

runProverT :: ProverFuncs
    -> String -- name
    -> ProverStateTHF
    -> GenericConfig ProofTree -- ^ configuration to use
    -> Bool -- ^ True means save THF file
    -> String -- ^ name of the theory in the DevGraph
    -> Named THFFormula -- ^ goal to prove
    -> IO (ATPRetval, GenericConfig ProofTree)
    -- ^ (retval, configuration with proof status and complete output)
runProverT d name pst cfg saveTHF thName nGoal = do
    let tout = cfgTimeout d cfg
        tmpFileName = thName ++ '_' : AS_Anno.senAttr nGoal
    prob <- showProblemTHF pst nGoal []
    runRes <- runProverProcess d cfg tout saveTHF tmpFileName prob
    case runRes of
        Nothing -> return (ATPTLimitExceeded, cfg
                        { proofStatus =
                            (openProofStatus (AS_Anno.senAttr nGoal)
                                            name emptyProofTree)
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
                _ | szsProved exitCode -> (ATPSuccess, provedStatus)
                _ | szsDisproved exitCode -> (ATPSuccess, disProvedStatus)
                _ | szsTimeout exitCode ->
                                    (ATPTLimitExceeded, defaultProofStatus)
                _ | szsStopped exitCode ->
                                    (ATPBatchStopped, defaultProofStatus)
                _ ->
                                    (ATPError exitCode, defaultProofStatus)
             defaultProofStatus =
              (openProofStatus (AS_Anno.senAttr nGoal) name emptyProofTree)
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

runProverProcess
    :: ProverFuncs
    -> GenericConfig ProofTree -- config
    -> Int -- ^ timeout time in seconds
    -> Bool -- ^ save problem
    -> String -- ^ filename without extension
    -> String -- ^ problem
    -> IO (Maybe (String, [String], Int))
runProverProcess d cfg tout saveTHF tmpFileName prob = do
    let tmpFile = basename tmpFileName ++ ".p"
    writeFile tmpFile prob
    (cmd, args) <- proverCommand d tout tmpFile cfg
    mres <- timeoutCommand tout cmd args
    maybe (return Nothing) (\ (_, pout, perr) -> do
        let l = lines pout
            (res', _, tUsed) = parseOutput d l
            res = getMessage d res' pout perr
        unless saveTHF $ removeFile tmpFile
        return $ Just (res, l, tUsed)) mres

-- parse the output and return the szsStatus and the used time.
parseOutput :: ProverFuncs -> [String] -> (String, Bool, Int)
  -- ^ (exit code, status found, used time ins ms)
parseOutput d = foldl checkLine ("", False, -1) where
   checkLine (exCode, stateFound, to) line = case getSZSStatusWord line of
        Just szsState | not stateFound -> (szsState, True, to)
        _ -> case getTimeUsed d line of
              Just secs -> (exCode, stateFound, secs)
              Nothing -> (exCode, stateFound, to)

-- try to read the szs status from a given String
getSZSStatusWord :: String -> Maybe String
getSZSStatusWord line =
    case words (fromMaybe "" $ stripPrefix "% SZS status" line) of
        [] -> Nothing
        w : _ -> Just w
