{- |
Module      :  $Header$
Description :  Interface to the theorem prover e-krhyper in CASC-mode.
Copyright   :  (c) Dominik Luecke, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Check out
http://www.uni-koblenz.de/~bpelzer/ekrhyper/
for details. For the ease of maintenance we are using e-krhyper in
its CASC-mode, aka tptp-input. It works for single input files and
fof-style.
-}

module SoftFOL.ProveHyperHyper (hyperProver)
    where

import Logic.Prover

import Common.ProofTree
import qualified Common.Result as Result
import Common.AS_Annotation as AS_Anno

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import GUI.GenericATP
import Proofs.BatchProcessing
import Interfaces.GenericATPState

import System.IO
import System.Process
import System.Posix.Time
import System.Directory

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent

import Common.Utils(trim)
import Data.List

import Data.Time (timeToTimeOfDay)
import Data.Time.LocalTime(TimeOfDay(..))
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

{- | The Prover implementation. -}
hyperProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
hyperProver = mkAutomaticProver "ekrhyper" () hyperGUI hyperCMDLautomaticBatch

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
           -- ^ theory consisting of a SoftFOL.Sign.Sign
           --   and a list of Named SoftFOL.Sign.Sentence
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
hyperGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName hyperProver) thName th
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
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
hyperCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName hyperProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

prelTxt :: Int -> String
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
    "#(start_wallclock_timer("++ show t ++".0)).\n"

runTxt :: String
runTxt =
    "% start derivation with the input received so far\n" ++
    "#(run).\n\n" ++
    "% print normal E-KRHyper proof\n" ++
    "%#(print_proof).\n\n" ++
    "% print result and proof using SZS terminology;\n" ++
    "% requires postprocessing with post_szs script for proper legibility\n" ++
    "%#(print_szs_proof).\n"

runHyper :: SoftFOLProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runHyper sps cfg saveTPTP thName nGoal =
    let
        saveFile = thName++'_':AS_Anno.senAttr nGoal
        tmpFile  = (reverse $ fst $ span (/='/') $ reverse thName) ++
                       '_':AS_Anno.senAttr nGoal
        prelFile = "prelude_" ++ (reverse $ fst $ span (/='/') $ reverse
                                          thName)
                   ++ '_':AS_Anno.senAttr nGoal
        runFile  = "run_" ++ (reverse $ fst $ span (/='/') $ reverse
                                          thName)
                   ++ '_':AS_Anno.senAttr nGoal
        simpleOptions = extraOpts cfg
        tl = configTimeLimit cfg
    in
      do
        prob <- showTPTPProblem thName sps nGoal $
                      simpleOptions ++ ["Requested prover: ekrhyper"]
        when saveTPTP
            (writeFile (saveFile ++".tptp") prob)
        t <- getCurrentTime
        let stpTmpFile  = "/tmp/" ++ tmpFile ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".tptp"
            stpPrelFile = "/tmp/" ++ prelFile ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".tme"
            stpRunFile  = "/tmp/" ++ runFile ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".tme"
        writeFile stpPrelFile $ prelTxt tl
        writeFile stpRunFile  $ runTxt
        writeFile stpTmpFile  $ prob
        let command = "ekrh " ++ stpPrelFile ++ " " ++ stpTmpFile ++
                      " " ++ stpRunFile
        t_start <- epochTime
        (_, stdouth, stderrh, proch) <- runInteractiveCommand command
        waitForProcess proch
        t_end <- epochTime
        removeFile stpPrelFile
        removeFile stpRunFile
        removeFile stpTmpFile
        let t_t = (round (realToFrac (t_end - t_start + 1) :: Double) :: Integer)
        let t_u = timeToTimeOfDay $ secondsToDiffTime $
                  if t_t == 0
                  then
                      1
                  else
                      t_t
        stdoutC <- hGetContents stdouth
        stderrC <- hGetContents stderrh
        (pStat, ret) <- examineProof sps cfg stdoutC stderrC simpleOptions nGoal t_u
        return (pStat, cfg
                         {
                           proofStatus = ret
                         , resultOutput = lines (stdoutC ++ stderrC)
                         , timeUsed = usedTime ret
                         })

{- | Mapping type from SZS to Hets -}
data HyperResult = HProved | HDisproved | HTimeout | HError | HMemout

{- | examine SZS output -}
examineProof :: SoftFOLProverState
             -> GenericConfig ProofTree
             -> String
             -> String
             -> [String]
             -> AS_Anno.Named SPTerm
             -> TimeOfDay
             -> IO (ATPRetval, ProofStatus ProofTree)
examineProof sps cfg stdoutC stderrC simpleOptions nGoal tUsed =
    let
        tScript opts = TacticScript $ show ATPTacticScript
                       { tsTimeLimit = configTimeLimit cfg
                       , tsExtraOpts = opts }
        defaultStatus =
            ProofStatus { goalName = senAttr nGoal
                        , goalStatus = openGoalStatus
                        , usedAxioms = []
                        , usedProver = proverName hyperProver
                        , proofTree =  emptyProofTree
                        , usedTime = tUsed
                        , tacticScript = tScript simpleOptions}
        out = filter ("% SZS status " `isPrefixOf`) $
              lines (stdoutC ++ stderrC)
        getAxioms =
            let
                fl = formulaLists $ initialLogicalPart sps
                fs = concatMap formulae $ filter (\x ->
                                                      case originType x of
                                                        SPOriginAxioms -> True
                                                        _              -> False
                                                 ) fl
            in map AS_Anno.senAttr fs
    in
    do
      if (length out /= 1)
       then
           return (ATPError ("Internal Error in ekrhyper.\nOutput was:\n\n" ++
                            stdoutC ++ stderrC), defaultStatus)
       else
           do
             let outp = map (trim . drop (length "% SZS status ")) out
             let res = case outp of
                         ["Theorem"]            -> HProved
                         ["Satisfiable"]        -> HProved
                         ["Timeout"]            -> HTimeout
                         ["CounterSatisfiable"] -> HDisproved
                         ["Unsatisfiable"]      -> HDisproved
                         ["MemoryOut"]          -> HMemout
                         _                      -> HError
             case res of
               HProved -> return (ATPSuccess, defaultStatus
                                  {
                                    goalStatus = Proved True
                                  , usedAxioms = getAxioms
                                  , proofTree  = ProofTree $ unlines out
                                  })
               HTimeout -> return (ATPTLimitExceeded, defaultStatus)
               HDisproved -> return (ATPSuccess, defaultStatus
                                     {
                                       goalStatus = Disproved
                                     , usedAxioms = getAxioms
                                     , proofTree  = ProofTree $ unlines out
                                     })
               HMemout -> return (ATPError ("Out of Memory."
                                           ++ "\nOutput was:\n\n" ++
                                              stdoutC ++ stderrC)
                                , defaultStatus)
               HError -> return (ATPError ("Internal Error in ekrhyper."
                                           ++ "\nOutput was:\n\n" ++
                                              stdoutC ++ stderrC)
                                , defaultStatus)
