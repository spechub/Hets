{- |
Module      :  $Header$
Copyright   :  (c) Domink Luecke, Uni Bremen 2009-2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Fact++ prover for OWL
-}

module OWL.ProveFact where

import Logic.Prover

import OWL.AS
import OWL.Morphism
import OWL.Sign
import OWL.Print
import OWL.Sublogic

import GUI.GenericATP
import Interfaces.GenericATPState

import Proofs.BatchProcessing

import Common.AS_Annotation
import Common.ProofTree
import qualified Common.Result as Result
import Common.Utils

import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)
import System.Posix.Time

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Concurrent
import Control.Monad (when)
import Control.Concurrent.MVar

import Data.Maybe

data FactProverState = FactProverState
                           { ontologySign :: Sign
                           , initialState :: [Named Axiom]
                           } deriving (Show)

data FactProblem = FactProblem
                       { identifier :: String
                       , problemProverState :: FactProverState
                       } deriving (Show)

-- * Prover implementation
factProverState :: Sign
                  -> [Named Axiom]
                  -> [FreeDefMorphism Axiom OWLMorphism]
                  -- ^ freeness constraints
                  -> FactProverState
factProverState sig oSens _ = FactProverState
  { ontologySign = sig
  , initialState = filter isAxiom oSens }

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
factProver :: Prover Sign Axiom OWLMorphism OWLSub ProofTree
factProver = mkAutomaticProver "Fact" sl_top factGUI
  factCMDLautomaticBatch

{- |
  Invokes the generic prover GUI.
-}
factGUI :: String -- ^ theory name
          -> Theory Sign Axiom ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
factGUI thName th freedefs =
  genericATPgui (atpFun thName) True (proverName factProver) thName th
                freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Fact prover.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
factCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Axiom ProofTree -- ^ theory
        -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
        -> IO (ThreadId, MVar ())
        -- ^ fst: identifier of the batch thread for killing it
        --   snd: MVar to wait for the end of the thread
factCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                         thName defTS th freedefs =
  genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
    resultMVar (proverName factProver) thName
    (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  The Cons-Checker implementation.
-}
factConsChecker :: ConsChecker Sign Axiom OWLSub OWLMorphism ProofTree
factConsChecker = mkConsChecker "Fact" sl_top consCheck

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Axiom OWLMorphism ProofTree FactProverState
atpFun thName = ATPFunctions
  { initialProverState = factProverState
  , atpTransSenName = id   -- transSenName,
  , atpInsertSentence = insertOWLAxiom
  , goalOutput = showOWLProblem thName
  , proverHelpText = "Fact++"
  , batchTimeEnv = "HETS_FACT_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions { problemOutput = ".owl"  -- owl-hets
                                    ,  proverOutput = ".fact"
                                    ,  theoryConfiguration = ".pconf" }
  , runProver = runFact
  , createProverOptions = extraOpts }

{- |
  Inserts a named OWL axiom into pellet prover state.
-}
insertOWLAxiom :: FactProverState -- ^ prover state containing
                                    --   initial logical part
               -> Named Axiom -- ^ goal to add
               -> FactProverState
insertOWLAxiom pps s = pps { initialState = initialState pps ++ [s] }

-- * Main prover functions
getEnvSec :: String -> IO String
getEnvSec s = getEnvDef s ""

{- |
  Runs the Fact++ consistency checker.
-}
consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName _ tm freedefs = case tTarget tm of
  Theory sig nSens ->
   do
    let saveOWL = False
        proverStateI = factProverState sig (toNamedList nSens) freedefs
        problemS     = showOWLProblemS thName proverStateI []
        saveFileName  = reverse $ fst $ span (/='/') $ reverse thName
        tmpFileName   = saveFileName
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ out ++ "\n\n" ++ problemS
          , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime $ tUsed }
    when saveOWL (writeFile (saveFileName ++".owl") problemS)
    t <- getCurrentTime
    tempDir <- getTemporaryDirectory
    pPath <- getEnvSec "HETS_OWL_TOOLS"
    setCurrentDirectory pPath
    let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                                                 ++ "-" ++ show (utctDayTime t) ++ ".owl"
        tmpURI = "file://" ++ timeTmpFile
        command = "java -Djava.library.path=lib/native/`uname -m` -jar " ++ pPath ++ "/OWLFact.jar " ++ tmpURI
    writeFile timeTmpFile problemS
    t_start <- epochTime
    (_, outh, errh, proch) <- runInteractiveCommand command
    ex_code <- waitForProcess proch
    t_end <- epochTime
    let t_u = round (realToFrac (t_end - t_start) :: Double)
    outp <- hGetContents outh
    eOut <- hGetContents errh
    removeFile timeTmpFile
    let cRes = case ex_code of
                 ExitFailure 10 -> (pStatus (outp ++ eOut) t_u) { ccResult = Just True }
                 ExitFailure 20 -> (pStatus (outp ++ eOut) t_u) { ccResult = Just False}
                 _              -> (pStatus (outp ++ eOut) t_u) { ccResult = Nothing}
    return $ cRes

showOWLProblemS :: String -- ^ theory name
                -> FactProverState -- ^ prover state containing
                                     -- initial logical part
                -> [String] -- ^ extra options
                -> String -- ^ formatted output of the goal
showOWLProblemS thName pst _ =
    let namedSens = initialState $ problemProverState
                    $ genFactProblemS thName pst Nothing
        sign      = ontologySign $ problemProverState
                    $ genFactProblemS thName pst Nothing
    in show $ printOWLBasicTheory (sign, filter isAxiom namedSens)

genFactProblemS :: String
                  -> FactProverState
                  -> Maybe (Named Axiom)
                  -> FactProblem
genFactProblemS thName pps m_nGoal = FactProblem
  { identifier = thName
  , problemProverState =
      pps { initialState = initialState pps ++ maybe [] (:[]) m_nGoal } }

{- |
  Pretty printing DL goal in Manchester-OWL-Syntax.
-}
showOWLProblem :: String -- ^ theory name
               -> FactProverState -- ^ prover state containing
                                    -- initial logical part
               -> Named Axiom -- ^ goal to print
               -> [String] -- ^ extra options
               -> IO String -- ^ formatted output of the goal
showOWLProblem thName pst nGoal _ =
  let namedSens = initialState $ problemProverState
                    $ genFactProblemS thName pst Nothing
      sign      = ontologySign $ problemProverState
                    $ genFactProblemS thName pst Nothing
  in return $ show (printOWLBasicTheory (sign, filter isAxiom namedSens))
       ++ "\n\nEntailments:\n\n" ++ show (printOWLBasicTheory (sign, [nGoal]))

{- |
   Invocation of the Fact Prover.
-}
runFact :: FactProverState
          -- ^ logical part containing the input Sign and axioms and possibly
          --   goals that have been proved earlier as additional axioms
          -> GenericConfig ProofTree -- ^ configuration to use
          -> Bool -- ^ True means save TPTP file
          -> String -- ^ name of the theory in the DevGraph
          -> Named Axiom -- ^ goal to prove
          -> IO (ATPRetval, GenericConfig ProofTree)
          -- ^ (retval, configuration with proof status and complete output)
runFact sps cfg saveFact thName nGoal = do
      let prob   = showOWLProblemS thName sps []
          entail = showOWLProblemS thName
                     (sps { initialState = [ nGoal {isAxiom = True } ] }) []
      when saveFact $ do writeFile (saveFileName ++".owl") prob
                         writeFile (saveFileName ++".entail.owl") entail
      t <- getCurrentTime
      tempDir <- getTemporaryDirectory
      let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                                ++ "-" ++ show (utctDayTime t) ++ ".owl"
          entailsFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                          ++ "-" ++ show (utctDayTime t) ++ ".entails.owl"
      writeFile timeTmpFile prob
      writeFile entailsFile entail
      pPath <- getEnvSec "HETS_OWL_TOOLS"
      let command = "java -Djava.library.path=lib/native/`uname -m` -jar " ++
                    pPath ++ "/OWLFactProver.jar file://" ++ timeTmpFile ++
                    " file://" ++ entailsFile
      setCurrentDirectory pPath
      t_start <- epochTime
      (mExit, outh, errh) <- timeoutCommand tLimit command
      t_end <- epochTime
      let t_u = round (realToFrac (t_end - t_start) :: Double)
      ((err, retval),output, tUsed) <- if isJust mExit then do
        output  <- hGetContents outh
        eOut    <- hGetContents errh
        let outp = lines $ output ++ eOut
        return (proofStat (fromJust mExit) simpleOptions outp t_u, outp, t_u)
        else return
          ((ATPTLimitExceeded, defaultProofStatus simpleOptions), [], tLimit)
      removeFile timeTmpFile
      removeFile entailsFile
      return (err, cfg { proofStatus = retval
                       , resultOutput = output
                       , timeUsed =
                           timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed
                       })
  where
    simpleOptions = extraOpts cfg
    tLimit        = fromMaybe 800 $ timeLimit cfg
    goalSuffix    = '_' : senAttr nGoal
    saveFileName  = thName ++ goalSuffix
    tmpFileName   = reverse (takeWhile (/= '/') $ reverse thName) ++ goalSuffix
    proofStat exitCode options out tUsed = case exitCode of
      ExitFailure 10 -> (ATPSuccess, (provedStatus options tUsed)
                       { usedAxioms = map senAttr $ initialState sps })
      ExitFailure 20 -> (ATPSuccess, disProvedStatus options)
      ExitFailure _ -> ( ATPError (unlines ("Internal error.":out))
                       , defaultProofStatus options)
      ExitSuccess -> ( ATPError (unlines ("Internal error.":out))
                       , defaultProofStatus options)
    tScript opts = TacticScript $ show ATPTacticScript
                     { tsTimeLimit = configTimeLimit cfg
                     , tsExtraOpts = opts }
    defaultProofStatus opts =
      (openProofStatus (senAttr nGoal) (proverName factProver) emptyProofTree)
        { tacticScript = tScript opts }
    disProvedStatus opts = (defaultProofStatus opts) {goalStatus = Disproved}
    provedStatus opts ut =
      ProofStatus { goalName = senAttr nGoal
                  , goalStatus = Proved True
                  , usedAxioms = []
                  , usedProver = proverName factProver
                  , proofTree =  emptyProofTree
                  , usedTime =
                      timeToTimeOfDay $ secondsToDiffTime $ toInteger ut
                  , tacticScript = tScript opts }
