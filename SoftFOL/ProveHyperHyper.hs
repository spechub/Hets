{- |
Module      :  $Header$
Description :  Interface to the theorem prover e-krhyper in CASC-mode.
Copyright   :  (c) Dominik Luecke, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Check out
http://www.uni-koblenz.de/~bpelzer/ekrhyper/
for details. For the ease of maintenance we are using e-krhyper in
its CASC-mode, aka tptp-input. It works for single input files and
fof-style.
-}

module SoftFOL.ProveHyperHyper (hyperProver, hyperConsChecker)
    where

import Logic.Prover

import Common.ProofTree
import qualified Common.Result as Result
import Common.AS_Annotation as AS_Anno
import Common.SZSOntology
import Common.Timing
import Common.Utils

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import GUI.GenericATP
import Proofs.BatchProcessing
import Interfaces.GenericATPState

import System.Process
import System.Directory

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Data.Char
import Data.List
import Data.Maybe

import Data.Time.LocalTime (TimeOfDay, midnight)

-- Prover

ekrhyperS :: String
ekrhyperS = "ekrhyper"

-- | The Prover implementation.
hyperProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
hyperProver = mkAutomaticProver ekrhyperS () hyperGUI hyperCMDLautomaticBatch

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
  , proverHelpText = "for more information visit " ++
                     "http://www.uni-koblenz.de/~bpelzer/ekrhyper/"
  , batchTimeEnv = "HETS_HYPER_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".hyper"
      , theoryConfiguration = ".hypcf" }
  , runProver = runHyper
  , createProverOptions = extraOpts }

{- |
  Invokes the generic prover GUI.
-}
hyperGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           {- ^ theory consisting of a SoftFOL.Sign.Sign
           and a list of Named SoftFOL.Sign.Sentence -}
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
hyperGUI thName th freedefs =
    genericATPgui (atpFun thName) True ekrhyperS thName th
                  freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the prover.
-}
hyperCMDLautomaticBatch ::
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
hyperCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar ekrhyperS thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

prelTxt :: String -> String
prelTxt t =
    "% only print essential output\n" ++
    "#(set_verbosity(1)).\n\n" ++
    "% assume all input to be in tptp-syntax\n" ++
    "#(set_parameter(input_type, 2)).\n\n" ++
    "% To prevent blowing up my memory\n" ++
    "#(set_memory_limit(500)).\n\n" ++
    "% produce SZS results\n" ++
    "#(set_flag(szs_output_flag, true)).\n\n" ++
    "% do not use special evaluable symbols\n" ++
    "#(clear_builtins).\n\n" ++
    "% initial term weight bound, 3 recommended for TPTP-problems\n" ++
    "#(set_parameter(max_weight_initial, 3)).\n\n" ++
    "% Terminate if out of memory\n" ++
    "#(set_parameter(limit_termination_method,0)).\n\n" ++
    "% Terminate if out of time\n" ++
    "#(set_parameter(timeout_termination_method,0)).\n\n" ++
    "% Start timer\n" ++
    "#(start_wallclock_timer(" ++ t ++ ".0)).\n"

checkOption :: String -> Bool
checkOption a = isPrefixOf "#(" a && isSuffixOf ")." a

uniteOptions :: [String] -> [String]
uniteOptions opts =
    case opts of
      a : b : cs ->
          if checkOption a
           then
               a : uniteOptions (b : cs)
           else
               (a ++ b) : uniteOptions cs
      _ -> opts

runTxt :: String
runTxt =
    "% start derivation with the input received so far\n" ++
    "#(run).\n\n" ++
    "% print normal E-KRHyper proof\n" ++
    "%#(print_proof).\n\n" ++
    "% print result and proof using SZS terminology;\n" ++
    "% requires postprocessing with post_szs script for proper legibility\n" ++
    "#(print_szs_proof).\n"

runHyper :: SoftFOLProverState
           {- ^ logical part containing the input Sign and axioms and possibly
           goals that have been proved earlier as additional axioms -}
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runHyper sps cfg saveTPTP thName nGoal =
    let
        saveFile = basename thName ++ '_' : AS_Anno.senAttr nGoal ++ ".tptp"
        simpleOptions = uniteOptions $ extraOpts cfg
        tl = configTimeLimit cfg
        tScript = TacticScript $ show ATPTacticScript
          { tsTimeLimit = tl
          , tsExtraOpts = filter (isPrefixOf "#")
              $ lines $ prelTxt (show tl) ++ runTxt }
        defProofStat = ProofStatus
          { goalName = senAttr nGoal
          , goalStatus = openGoalStatus
          , usedAxioms = []
          , usedProver = ekrhyperS
          , proofTree = emptyProofTree
          , usedTime = midnight
          , tacticScript = tScript }
    in
        if all checkOption simpleOptions
         then
           do
             prob <- showTPTPProblem thName sps nGoal []
             when saveTPTP (writeFile saveFile prob)
             (stdoutC, stderrC, t_u) <- runHyperProcess prob saveFile (show tl)
               ('\n' : unlines simpleOptions) runTxt
             let (pStat, ret) = examineProof sps stdoutC stderrC
                   defProofStat { usedTime = t_u }
             return (pStat, cfg
                              { proofStatus = ret
                              , resultOutput = lines (stdoutC ++ stderrC)
                              , timeUsed = usedTime ret })
         else return
                    (ATPError "Syntax error in options"
                    , cfg
                     { proofStatus = defProofStat
                     , resultOutput = ["Parse Error"]
                     , timeUsed = midnight
                     })

-- | call ekrh
runHyperProcess
  :: String -- ^ problem
  -> String -- ^ file name template
  -> String -- ^ time limit
  -> String -- ^ extra options
  -> String -- ^ run text
  -> IO (String, String, TimeOfDay) -- ^ out, err, diff time
runHyperProcess prob saveFile tl opts runTxtA = do
  stpTmpFile <- getTempFile prob saveFile
  let stpPrelFile = stpTmpFile ++ ".prelude.tme"
      stpRunFile = stpTmpFile ++ ".run.tme"
  writeFile stpPrelFile $ prelTxt tl ++ opts
  writeFile stpRunFile runTxtA
  t_start <- getHetsTime
  (_, stdoutC, stderrC) <- readProcessWithExitCode "ekrh"
    [stpPrelFile, stpTmpFile, stpRunFile] ""
  t_end <- getHetsTime
  removeFile stpPrelFile
  removeFile stpRunFile
  removeFile stpTmpFile
  return (stdoutC, stderrC, diffHetsTime t_end t_start)

-- | Mapping type from SZS to Hets
data HyperResult = HProved | HDisproved | HTimeout | HError | HMemout

getHyperResult :: [String] -> HyperResult
getHyperResult out = case map (takeWhile isAlpha . dropWhile isSpace)
    $ mapMaybe (stripPrefix "% SZS status ") out of
  [s] | szsProved s -> HProved
    | szsDisproved s -> HDisproved
    | szsTimeout s -> HTimeout
    | szsMemoryOut s -> HMemout
  _ -> HError

-- | examine SZS output
examineProof :: SoftFOLProverState
             -> String
             -> String
             -> ProofStatus ProofTree
             -> (ATPRetval, ProofStatus ProofTree)
examineProof sps stdoutC stderrC defStatus =
    let getAxioms =
            let
                fl = formulaLists $ initialLogicalPart sps
                fs = concatMap formulae $ filter (\ x ->
                                                      case originType x of
                                                        SPOriginAxioms -> True
                                                        _ -> False
                                                 ) fl
            in map AS_Anno.senAttr fs
        outText = "\nOutput was:\n\n" ++ stdoutC ++ stderrC
        provenStat = defStatus
          { usedAxioms = getAxioms
          , proofTree = ProofTree stdoutC }
     in case getHyperResult $ lines stdoutC of
               HProved -> (ATPSuccess, provenStat { goalStatus = Proved True })
               HTimeout -> (ATPTLimitExceeded, defStatus)
               HDisproved -> (ATPSuccess, provenStat { goalStatus = Disproved })
               HMemout -> (ATPError ("Out of Memory." ++ outText), defStatus)
               HError -> ( ATPError ("Internal Error in ekrhyper." ++ outText)
                         , defStatus)

-- Consistency Checker

hyperConsChecker :: ConsChecker Sign Sentence () SoftFOLMorphism ProofTree
hyperConsChecker = (mkConsChecker ekrhyperS () consCheck)
  { ccNeedsTimer = False }

{- |
  Runs the krhyper cons-chcker. The tactic script only contains a string for the
  time limit.
-}

runTxtC :: String
runTxtC =
    "% start derivation with the input received so far\n" ++
    "#(run).\n\n" ++
    "% print normal E-KRHyper proof\n" ++
    "%#(print_proof).\n\n" ++
    "% print result and proof using SZS terminology;\n" ++
    "% requires postprocessing with post_szs script for proper legibility\n" ++
    "%#(print_szs_proof).\n\n" ++
    "% Show the model\n" ++
    "#(print_model).\n"

consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Sentence SoftFOLMorphism ProofTree
          -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName (TacticScript tl) tm freedefs =
    case tTarget tm of
      Theory sig nSens -> do
          let proverStateI = spassProverState sig (toNamedList nSens) freedefs
              saveFile = basename thName ++ ".tptp"
          prob <- showTPTPProblemM thName proverStateI []
          (stdoutC, stderrC, t_u) <-
            runHyperProcess prob saveFile tl "" runTxtC
          return CCStatus
            { ccResult = case getHyperResult $ lines stdoutC of
                HProved -> Just True
                HDisproved -> Just False
                _ -> Nothing
            , ccProofTree = ProofTree $ stdoutC ++ stderrC
            , ccUsedTime = t_u }
