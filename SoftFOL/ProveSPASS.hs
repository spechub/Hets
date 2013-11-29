{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{-
      - check if the theorem is used in the proof;
        if not, the theory is inconsistent;
        mark goal as proved and emmit a warning...

      - Implement a consistency checker based on GUI
-}

module SoftFOL.ProveSPASS (spassProver, spassProveCMDLautomaticBatch) where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import GUI.GenericATP
import Interfaces.GenericATPState
import Proofs.BatchProcessing

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree
import Common.Utils

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Data.Char
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay (..), midnight)

-- * Prover implementation

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}

spassName :: String
spassName = "SPASS"

spassProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
spassProver = mkAutomaticProver spassName () spassProveGUI
  spassProveCMDLautomaticBatch

-- * Main prover functions

-- ** Utility functions

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
    , goalOutput = showDFGProblem thName
    , proverHelpText = "http://www.spass-prover.org/\n"
    , batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT"
    , fileExtensions = FileExtensions
        { problemOutput = ".dfg"
        , proverOutput = ".spass"
        , theoryConfiguration = ".spcf"}
    , runProver = runSpass
    , createProverOptions = createSpassOptions }

{- |
  Parses a given default tactic script into a
  'Interfaces.GenericATPState.ATPTacticScript' if possible. Otherwise a default
  SPASS tactic script is returned.
-}
parseSpassTacticScript :: TacticScript
                        -> ATPTacticScript
parseSpassTacticScript =
    parseTacticScript batchTimeLimit ["-Stdin", "-DocProof"]

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
spassProveGUI :: String -- ^ theory name
          -> Theory Sign Sentence ProofTree {- ^ theory consisting of a
             'SPASS.Sign.Sign' and a list of Named 'SPASS.Sign.Sentence' -}
          -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
          -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
spassProveGUI thName th freedefs =
    genericATPgui (atpFun thName) True spassName thName th
                  freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the SPASS prover.
  SPASS specific functions are omitted by data type ATPFunctions.
-}
spassProveCMDLautomaticBatch ::
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
spassProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar spassName thName
        (parseSpassTacticScript defTS) th freedefs emptyProofTree


-- * SPASS Interfacing Code

{- |
  Reads and parses the output of SPASS.
-}
parseSpassOutput :: [String] -- ^ the SPASS process output
                 -> (Maybe String, [String], Bool, TimeOfDay)
                    -- ^ (result, used axioms, complete output, used time)
parseSpassOutput = foldl parseIt (Nothing, [], False, midnight)
  where
    parseIt (res, usedAxs, startFound, tUsed) line =
          ( case stripPrefix "SPASS beiseite: " line of
             r@(Just _) | startFound -> r
             _ -> res
          , case stripPrefix "Formulae used in the proof :" line of
             Just s -> words s
             Nothing -> usedAxs
          , startFound || isInfixOf "SPASS-START" line
          , case stripPrefix "SPASS spent" line of
              Just s | isInfixOf "on the problem." line ->
                fromMaybe midnight $ parseTimeOfDay
                        $ takeWhile (\ c -> isDigit c || elem c ".:")
                        $ trimLeft s
              _ -> tUsed)

parseTimeOfDay :: String -> Maybe TimeOfDay
parseTimeOfDay str =
    case splitOn ':' str of
      [h, m, s] -> Just TimeOfDay
        { todHour = read h
        , todMin = read m
        , todSec = realToFrac (read s :: Double) }
      _ -> Nothing

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SoftFOLProverState {- ^ logical part containing the input Sign and
                     axioms and possibly goals that have been proved
                     earlier as additional axioms -}
         -> GenericConfig ProofTree -- ^ configuration to use
         -> Bool -- ^ True means save DFG file
         -> String -- ^ name of the theory in the DevGraph
         -> AS_Anno.Named SPTerm -- ^ goal to prove
         -> IO (ATPRetval, GenericConfig ProofTree)
             -- ^ (retval, configuration with proof status and complete output)
runSpass sps cfg saveDFG thName nGoal = do
  let allOptions = "-Stdin" : createSpassOptions cfg
      extraOptions = "-DocProof" : cleanOptions cfg
  prob <- showDFGProblem thName sps nGoal (createSpassOptions cfg)
  when saveDFG
    $ writeFile (basename thName ++ '_' : AS_Anno.senAttr nGoal ++ ".dfg") prob
  (_, pout, _) <- executeProcess spassName allOptions prob
  -- SPASS 3.7 does not properly stop, but fails with an exit code
  let out = lines pout
      (res, usedAxs, startFound, tUsed) = parseSpassOutput out
      defaultProofStatus =
        (openProofStatus (AS_Anno.senAttr nGoal) spassName
                           emptyProofTree)
        {tacticScript = TacticScript $ show ATPTacticScript
          {tsTimeLimit = configTimeLimit cfg,
           tsExtraOpts = extraOptions} }
      (err, retval) = case res of
        Nothing -> (ATPError $ "Found no SPASS "
          ++ if startFound then "result" else "output"
          , defaultProofStatus)
        Just str
          | isInfixOf "Proof found." str ->
            (ATPSuccess, defaultProofStatus
             { goalStatus = Proved $ elem (AS_Anno.senAttr nGoal) usedAxs
             , usedAxioms = filter (/= AS_Anno.senAttr nGoal) usedAxs
             , proofTree = ProofTree $ spassProof out })
          | isInfixOf "Completion found." str ->
            (ATPSuccess, defaultProofStatus
             { goalStatus = Disproved } )
          | isInfixOf "Ran out of time." str ->
            (ATPTLimitExceeded, defaultProofStatus)
        _ -> (ATPSuccess, defaultProofStatus)
  return (err, cfg
    { proofStatus = retval
    , resultOutput = out
    , timeUsed = tUsed })

{- |
  Creates a list of all options the SPASS prover runs with.
  That includes the defaults -DocProof and -Timelimit.
-}
createSpassOptions :: GenericConfig ProofTree -> [String]
createSpassOptions cfg =
    cleanOptions cfg ++ ["-DocProof", "-TimeLimit="
                             ++ show (configTimeLimit cfg)]

{- |
  Filters extra options and just returns the non standard options.
-}
cleanOptions :: GenericConfig ProofTree -> [String]
cleanOptions cfg =
    filter (\ opt -> not $ any (`isPrefixOf` opt) filterOptions)
           (extraOpts cfg)
    where
      filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]

{- |
  Extract proof tree from SPASS output. This will be the String between
  "Here is a proof" and "Formulae used in the proof"
-}
spassProof :: [String] -- ^ SPASS output containing proof tree
           -> String -- ^ extracted proof tree
spassProof =
        unlines . takeWhile (isPrefixOf "Formulae used in the proof")
             . (\ l -> if null l then l else tail l)
             . dropWhile (isPrefixOf "Here is a proof with depth")
