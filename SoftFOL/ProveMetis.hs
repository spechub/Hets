module SoftFOL.ProveMetis
  ( metisProver, metisProveCMDLautomaticBatch) where


import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result

import Common.ProofTree

import GUI.GenericATP
import Interfaces.GenericATPState
import Proofs.BatchProcessing

import System.IO
import System.Directory
import System.Exit
import Common.Utils
import Data.Time.Clock
import Data.Time.LocalTime
import Data.List
import Maybe

import Control.Monad
import qualified Control.Concurrent as Concurrent


{- | The Prover implementation. -}
metisProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
metisProver = mkAutomaticProver "metis" () metisGUI
  metisProveCMDLautomaticBatch

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
  , proverHelpText = ""
  , batchTimeEnv = ""
  , fileExtensions = FileExtensions
      { problemOutput = ".tptp"
      , proverOutput = ".spass"
      , theoryConfiguration = ""  }
  , runProver = runMetis
  , createProverOptions = extraOpts }


{- |
  Invokes the generic prover GUI.
-}
metisGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a SoftFOL.Sign.Sign
           --   and a list of Named SoftFOL.Sign.Sentence
           -> [FreeDefMorphism SPTerm SoftFOLMorphism] -- ^ freeness constraints
           -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
metisGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName metisProver) thName th
                  freedefs emptyProofTree


-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Metis prover.
-}

metisProveCMDLautomaticBatch ::
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
metisProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName metisProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree


runMetis :: SoftFOLProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runMetis sps cfg saveTPTP thName nGoal = do
  let
        saveFile = thName++'_':AS_Anno.senAttr nGoal
        myTimeLimit = configTimeLimit cfg

  prob <- showTPTPProblem thName sps nGoal $ []
  when saveTPTP
      (writeFile (saveFile++".tptp") prob)
  tmppath <- getTemporaryDirectory
  (timeTmpFile,temphandel) <- openTempFile tmppath "tmp.tptp"
  hPutStr temphandel prob
  hClose temphandel
  let command = "metis " ++( concat(extraOpts cfg))++ " " ++ timeTmpFile
  --recording time
  start <- liftM utctDayTime $ getCurrentTime
  (end,outh,errh)<- timeoutCommand myTimeLimit command
  finish <- liftM utctDayTime $ getCurrentTime
  --system"killall metis"
  let executetime = timeToTimeOfDay $ finish - start
  removeFile timeTmpFile
  out <- liftM lines $ hGetContents outh
  err <- liftM lines $ hGetContents errh
  -- parsing output from timeoutCommand
  case end of
       Nothing  ->      return(ATPTLimitExceeded,cfg{	timeLimitExceeded= True,
               					resultOutput=["TimeOut"]++out ++ err,
               					timeUsed= executetime,
  						proofStatus= (proofStatus cfg){usedTime=executetime}
  						})
       Just ExitSuccess -> return(ATPSuccess,cfg{resultOutput=out++err,
   					   timeUsed= executetime,
		 			   proofStatus= (proofStatus cfg){usedAxioms= getAxioms sps,
									goalStatus= getGoalStatus $ words $ fromJust(find (isPrefixOf "SZS status")out ),
									usedTime=executetime
									}
					  })
       _ -> return(ATPError (unlines $ out++err), cfg{	resultOutput=out++err,
						timeUsed=executetime,
						proofStatus= (proofStatus cfg){usedTime=executetime}
						})
{-
  mapping from SZS Status to Goalstatus
-}
getGoalStatus :: [String] -> GoalStatus
getGoalStatus l= case l of
			(_:_:"Theorem":_) -> Proved True
 			(_:_:"Proved":_) -> Proved True
 			(_:_:"Satisfiable":_) -> Proved True
 			(_:_:"Disproved":_) ->  Disproved
 			(_:_:"CounterSatisfiable":_) -> Disproved
 			(_:_:"Unsatisfiable":_) -> Disproved
 			_ -> error $ concat $ l


{-
  from ProveDarwin.hs
-}
getAxioms :: SoftFOLProverState -> [String]
getAxioms sps =  map AS_Anno.senAttr $ concatMap formulae $ filter isAxiomFormula $ formulaLists $ initialLogicalPart sps

isAxiomFormula :: SPFormulaList -> Bool
isAxiomFormula fl =
    case originType fl of
      SPOriginAxioms -> True
      _              -> False



