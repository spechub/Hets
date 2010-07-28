{- |
Module      :  $Header$
Description :  Interface to the theorem prover e-krhyper in CASC-mode.
Copyright   :  (c) Dominik Luecke, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Check out
<http://www.uni-koblenz.de/~bpelzer/ekrhyper/>
for details. For the ease of maintenance we are using e-krhyper in
its CASC-mode, aka tptp-input. It works for single input files and
fof-style.
-}

module QBF.ProveDepQBF (depQBFProver)
    where

import Logic.Prover

import Common.ProofTree
import qualified Common.Result as Result
import Common.AS_Annotation as AS_Anno

import Propositional.Sign
import QBF.ProverState
import qualified QBF.AS_BASIC_QBF as AS
import QBF.Morphism
import QBF.Sublogic (QBFSL, top)

import GUI.GenericATP
import Proofs.BatchProcessing
import Interfaces.GenericATPState

import System.IO
import System.Process
import System.Posix.Time
import System.Directory

import Control.Monad (when)
import qualified Control.Concurrent as Concurrent
import System.Exit (ExitCode (..))

import Data.List

import Data.Time (timeToTimeOfDay)
import Data.Time.LocalTime (TimeOfDay (..))
import Data.Time.Clock (UTCTime (..), secondsToDiffTime, getCurrentTime)

-- Prover

-- | The Prover implementation.
depQBFProver :: Prover Sign AS.FORMULA Morphism QBFSL ProofTree
depQBFProver = mkAutomaticProver "depqbf" top depQBFGUI depQBFCMDLautomaticBatch

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
  -> ATPFunctions Sign AS.FORMULA Morphism ProofTree QBFProverState
atpFun thName = ATPFunctions
  { initialProverState = qbfProverState
  , atpTransSenName = transSenName
  , atpInsertSentence = insertSentence
  , goalOutput = showQDIMACSProblem thName
  , proverHelpText = "for more information visit " ++
                     "http://fmv.jku.at/depqbf/"
  , batchTimeEnv = ""
  , fileExtensions = FileExtensions
      { problemOutput = ".qdimacs"
      , proverOutput = ""        -- prover doesn't output any files
      , theoryConfiguration = "" -- prover doesn't use any configuration files
      }
  , runProver = runDepQBF
  , createProverOptions = extraOpts }

{- |
  Invokes the generic prover GUI.
-}
depQBFGUI :: String -- ^ theory name
           -> Theory Sign AS.FORMULA ProofTree
           -> [FreeDefMorphism AS.FORMULA Morphism] -- ^ freeness constraints
           -> IO ([ProofStatus ProofTree]) -- ^ proof status for each goal
depQBFGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName depQBFProver) thName th
                  freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the prover.
-}
depQBFCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign AS.FORMULA ProofTree
        -> [FreeDefMorphism AS.FORMULA Morphism] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId, Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           -- snd: MVar to wait for the end of the thread
depQBFCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName depQBFProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

uniteOptions :: [String] -> String
uniteOptions = intercalate " "

runDepQBF :: QBFProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           -- goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save QDIMACS file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named AS.FORMULA -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runDepQBF ps cfg saveQDIMACS thName nGoal =
    let
        saveFile = thName ++ '_' : AS_Anno.senAttr nGoal
        tmpFile = reverse (fst $ span (/= '/') $ reverse thName) ++
                       '_' : AS_Anno.senAttr nGoal
        simpleOptions = uniteOptions $ extraOpts cfg
        tl = configTimeLimit cfg
    in
           do
             prob <- showQDIMACSProblem thName ps nGoal []
             when saveQDIMACS
                 (writeFile (saveFile ++ ".qdimacs") prob)
             t <- getCurrentTime
             let stpTmpFile = "/tmp/" ++ tmpFile ++ show (utctDay t) ++
                                    "-" ++ show (utctDayTime t) ++ ".qdimacs"
             writeFile stpTmpFile prob
             let command = "depqbf " ++ show tl ++ " "
                             ++ simpleOptions ++ " " ++ stpTmpFile
             t_start <- epochTime
             (_, stdouth, stderrh, proch) <- runInteractiveCommand command
             exitCode <- waitForProcess proch
             t_end <- epochTime
             removeFile stpTmpFile
             let t_t = (round (realToFrac
                               (t_end - t_start + 1) :: Double) :: Integer)
             let t_u = timeToTimeOfDay $ secondsToDiffTime $
                       if t_t == 0
                       then
                           1
                       else
                           t_t
             stdoutC <- hGetContents stdouth
             stderrC <- hGetContents stderrh
             let exitCode' = case exitCode of
                                  ExitSuccess -> 0
                                  ExitFailure i -> i
             (pStat, ret) <- examineProof ps cfg
               stdoutC stderrC exitCode' nGoal t_u tl
             return (pStat, cfg
                              {
                                proofStatus = ret
                              , resultOutput = lines (stdoutC ++ stderrC)
                              , timeUsed = usedTime ret
                             })

-- | examine Prover output
examineProof :: QBFProverState
             -> GenericConfig ProofTree
             -> String
             -> String
             -> Int
             -> AS_Anno.Named AS.FORMULA
             -> TimeOfDay
             -> Int
             -> IO (ATPRetval, ProofStatus ProofTree)
examineProof ps _ stdoutC _ exitCode nGoal tUsed _ =
    let
        defaultStatus =
            ProofStatus { goalName = senAttr nGoal
                        , goalStatus = openGoalStatus
                        , usedAxioms = []
                        , usedProver = proverName depQBFProver
                        , proofTree = emptyProofTree
                        , usedTime = tUsed
                        , tacticScript = TacticScript "" }
        getAxioms = map AS_Anno.senAttr (initialAxioms ps)
    in case getDepQBFResult exitCode stdoutC of
               DepQBFProved -> return (ATPSuccess, defaultStatus
                                  {
                                    goalStatus = Proved True
                                  , usedAxioms = getAxioms
                                  })
               DepQBFTimeout -> return (ATPTLimitExceeded, defaultStatus)
               DepQBFDisproved -> return (ATPSuccess, defaultStatus
                                     {
                                       goalStatus = Disproved
                                     , usedAxioms = getAxioms
                                     })
               DepQBFError s -> return (ATPError ("Internal Errorr."
                                           ++ "\nMessage:\n\n" ++ s)
                                , defaultStatus)

data DepQBFResult = DepQBFProved | DepQBFDisproved
                  | DepQBFTimeout | DepQBFError String

getDepQBFResult :: Int -> String -> DepQBFResult
getDepQBFResult exitCode out = case exitCode of
                                 10 -> if "SAT" `isPrefixOf` out
                                       then DepQBFProved
                                       else DepQBFError
                                         "Unexpected behaviour of prover!"
                                 20 -> if "UNSAT" `isPrefixOf` out
                                       then DepQBFDisproved
                                       else DepQBFError
                                         "Unexpected behaviour of prover!"
                                 _ -> if "SIGALRM" `isInfixOf` out
                                      then DepQBFTimeout
                                      else DepQBFError
                                        ("Uknown error: " ++ out)
