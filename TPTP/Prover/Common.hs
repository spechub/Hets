{- |
Module      :  ./TPTP/Prover/EProver.hs
Description :  Interface for the E Theorem Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Common where

import TPTP.Prover.ProverState
import TPTP.Morphism
import TPTP.Sign
import TPTP.Sublogic

import Common.AS_Annotation
import Common.ProofTree
import Common.Result
import Common.SZSOntology
import Common.Timing
import Common.Utils
import GUI.GenericATP
import Interfaces.GenericATPState hiding (proverState, timeUsed)
import Logic.Prover
import Proofs.BatchProcessing

import qualified Control.Concurrent as Concurrent
import Control.Monad
import Data.Char (toUpper)
import Data.Maybe
import Data.Time.LocalTime
import System.Directory
import System.Exit

type AtpFunType =
  String -> ATPFunctions Sign Sentence Morphism ProofTree ProverState

type RunTheProverType =
     ProverState
     {- ^ logical part containing the input Sign and axioms and possibly
     goals that have been proved earlier as additional axioms -}
  -> GenericConfig ProofTree -- ^ configuration to use
  -> Bool -- ^ True means save TPTP file
  -> String -- ^ name of the theory in the DevGraph
  -> Named Sentence -- ^ goal to prove
  -> IO (ATPRetval, GenericConfig ProofTree)
     -- ^ (retval, configuration with proof status and complete output)

mkProver :: String
         -> String
         -> Sublogic
         -> RunTheProverType
         -> Prover Sign Sentence Morphism Sublogic ProofTree
mkProver binary_name prover_name sublogics runTheProver =
  mkAutomaticProver binary_name prover_name sublogics proverGUI proverCLI
  where
    atpFun :: String
           -> ATPFunctions Sign Sentence Morphism ProofTree ProverState
    atpFun theoryName = ATPFunctions
      { initialProverState = tptpProverState,
        atpTransSenName = id,
        atpInsertSentence = insertSentenceIntoProverState,
        goalOutput = ioShowTPTPProblem theoryName,
        proverHelpText = helpText,
        batchTimeEnv = "HETS_" ++ map toUpper prover_name ++ "_BATCH_TIME_LIMIT",
        fileExtensions =
          FileExtensions { problemOutput = ".tptp"
                         , proverOutput = "."++ prover_name ++ ".out"
                         , theoryConfiguration = "." ++ prover_name ++ ".conf"
                         },
        runProver = runTheProver,
        createProverOptions = extraOpts}

    helpText :: String
    helpText =
      "No help yet available.\n" ++
      "Email hets-devel@informatik.uni-bremen.de " ++
      "for more information.\n"

    proverGUI :: String
              -> Theory Sign Sentence ProofTree
              -> [FreeDefMorphism Sentence Morphism]
              -> IO [ProofStatus ProofTree]
    proverGUI theoryName theory freenessConstraints =
      genericATPgui
        (atpFun theoryName)
        True
        prover_name
        theoryName
        theory
        freenessConstraints
        emptyProofTree

    proverCLI :: Bool
              -> Bool
              -> Concurrent.MVar (Result [ProofStatus ProofTree])
              -> String
              -> TacticScript
              -> Theory Sign Sentence ProofTree
              -> [FreeDefMorphism Sentence Morphism]
              -> IO (Concurrent.ThreadId, Concurrent.MVar ())
    proverCLI includeProvedTheorems saveProblemFile batchResultStore theoryName
                defaultTacticScript theory freenessConstraints =
      genericCMDLautomaticBatch
        (atpFun theoryName)
        includeProvedTheorems
        saveProblemFile
        batchResultStore
        prover_name
        theoryName
        (parseProverTacticScript defaultTacticScript)
        theory
        freenessConstraints
        emptyProofTree

    parseProverTacticScript :: TacticScript -> ATPTacticScript
    parseProverTacticScript = parseTacticScript batchTimeLimit []


mkTheoryFileName :: String -> Named Sentence -> String
mkTheoryFileName theoryName namedGoal =
  theoryName ++ '_' : senAttr namedGoal ++ ".tptp"

getTimeLimit :: GenericConfig ProofTree -> Int
getTimeLimit cfg = fromMaybe 100 $ timeLimit cfg

hardTimeLimit :: GenericConfig ProofTree -> Int
hardTimeLimit cfg =
  let configuredTimeLimit = getTimeLimit cfg
  in minimum [ configuredTimeLimit + 30
             , round ((1.5 :: Double) * fromIntegral configuredTimeLimit)
             ]

gnuTimeout :: IO String
gnuTimeout = do
  path <- findExecutable "gtimeout"
  return $ if isJust path then "gtimeout" else "timeout"


prepareProverInput :: ProverState
                   -> GenericConfig ProofTree
                   -> Bool
                   -> String
                   -> Named Sentence
                   -> String
                   -> IO String
prepareProverInput proverState cfg saveTPTPFile theoryName namedGoal prover_name =
  do
    let theoryFileName = mkTheoryFileName theoryName namedGoal
    tptpProblemString <- getProblemString
    problemFileName <- getTempFile tptpProblemString theoryFileName
    saveProblemFileIfNeeded theoryFileName tptpProblemString
    return problemFileName
  where
    getProblemString :: IO String
    getProblemString = ioShowTPTPProblem theoryName proverState namedGoal $
        extraOpts cfg ++ ["Requested prover: " ++ prover_name]

    saveProblemFileIfNeeded :: String -> String -> IO ()
    saveProblemFileIfNeeded theoryFileName tptpProblemString =
      when saveTPTPFile $ writeFile theoryFileName tptpProblemString

executeTheProver :: String -> [String] -> IO (ExitCode, [String], TimeOfDay)
executeTheProver binary_name options = do
  startTime <- getHetsTime
  (exitCode, pout, perr) <- executeProcess binary_name options ""
  endTime <- return exitCode >> getHetsTime
  let wallTimeUsed = diffHetsTime endTime startTime
  let out = lines (perr ++ pout)
  return (exitCode, out, wallTimeUsed)

atpRetValAndProofStatus :: GenericConfig ProofTree
                        -> Named Sentence
                        -> TimeOfDay
                        -> [String]
                        -> String
                        -> String
                        -> (ATPRetval, ProofStatus ProofTree)
atpRetValAndProofStatus cfg namedGoal timeUsed axiomsUsed szsStatusLine prover_name =
  let statuses = proofStatuses cfg namedGoal timeUsed axiomsUsed prover_name
  in selectRetValAndProofStatus statuses szsStatusLine

selectRetValAndProofStatus :: (ProofStatus ProofTree,
                               ProofStatus ProofTree,
                               ProofStatus ProofTree)
                           -> String
                           -> (ATPRetval, ProofStatus ProofTree)
selectRetValAndProofStatus (defaultPS, proved, disproved) szsStatusLine =
  case () of
    _ | szsProved szsStatusLine    -> (ATPSuccess, proved)
    _ | szsDisproved szsStatusLine -> (ATPSuccess, disproved)
    _ | szsTimeout szsStatusLine   -> (ATPTLimitExceeded, defaultPS)
    _ | szsStopped szsStatusLine   -> (ATPBatchStopped, defaultPS)
    _                              -> (ATPError szsStatusLine, defaultPS)

proofStatuses :: GenericConfig ProofTree
              -> Named Sentence
              -> TimeOfDay
              -> [String]
              -> String
              -> (ProofStatus ProofTree,
                  ProofStatus ProofTree,
                  ProofStatus ProofTree)
proofStatuses cfg namedGoal timeUsed axiomsUsed prover_name =
  let defaultPS =
        (openProofStatus (senAttr namedGoal) prover_name emptyProofTree)
          { usedTime = timeUsed
          , tacticScript = TacticScript $ show ATPTacticScript
             { tsTimeLimit = configTimeLimit cfg
             , tsExtraOpts = extraOpts cfg } }
      disproved = defaultPS { goalStatus = Disproved }
      proved = defaultPS
        { goalStatus = Proved True
        , usedAxioms = axiomsUsed
        , usedProver = prover_name
        , usedTime = timeUsed
        }
  in  (defaultPS, proved, disproved)
