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
import Common.ProverTools
import Common.Utils
import Common.Timing

import Data.Time.LocalTime (midnight)

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Concurrent
import Control.Monad (when)

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
          -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
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
        {- ^ fst: identifier of the batch thread for killing it
        snd: MVar to wait for the end of the thread -}
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
                                    , proverOutput = ".fact"
                                    , theoryConfiguration = ".pconf" }
  , runProver = runFact
  , createProverOptions = extraOpts }

{- |
  Inserts a named OWL axiom into pellet prover state.
-}
insertOWLAxiom :: FactProverState {- ^ prover state containing
                                    initial logical part -}
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
        problemS = showOWLProblemS thName proverStateI []
        tmpFileName = basename thName ++ ".owl"
        jar = "OWLFact.jar"
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ out ++ "\n\n" ++ problemS
          , ccUsedTime = tUsed }
    when saveOWL (writeFile tmpFileName problemS)
    (progTh, toolPath) <- check4HetsOWLjar jar
    if progTh then withinDirectory toolPath $ do
        tempDir <- getTemporaryDirectory
        timeTmpFile <- writeTempFile problemS tempDir tmpFileName
        let command = "java -Djava.library.path=lib/native/`uname -m` -jar "
              ++ jar ++ " file://" ++ timeTmpFile
        t_start <- getHetsTime
        (_, outh, errh, proch) <- runInteractiveCommand command
        ex_code <- waitForProcess proch
        t_end <- getHetsTime
        outp <- hGetContents outh
        eOut <- hGetContents errh
        removeFile timeTmpFile
        let t_u = diffHetsTime t_end t_start
            pStat = pStatus (outp ++ eOut) t_u
        return $ case ex_code of
          ExitFailure 10 -> pStat { ccResult = Just True }
          ExitFailure 20 -> pStat { ccResult = Just False}
          _ -> pStat
       else return $ pStatus "OWLFact not found" midnight

showOWLProblemS :: String -- ^ theory name
                -> FactProverState {- ^ prover state containing
                                     initial logical part -}
                -> [String] -- ^ extra options
                -> String -- ^ formatted output of the goal
showOWLProblemS thName pst _ =
    let namedSens = initialState $ problemProverState
                    $ genFactProblemS thName pst Nothing
        sign = ontologySign $ problemProverState
                    $ genFactProblemS thName pst Nothing
    in show $ printOWLBasicTheory (sign, filter isAxiom namedSens)

genFactProblemS :: String
                  -> FactProverState
                  -> Maybe (Named Axiom)
                  -> FactProblem
genFactProblemS thName pps m_nGoal = FactProblem
  { identifier = thName
  , problemProverState =
      pps { initialState = initialState pps ++ maybeToList m_nGoal } }

{- |
  Pretty printing DL goal in Manchester-OWL-Syntax.
-}
showOWLProblem :: String -- ^ theory name
               -> FactProverState {- ^ prover state containing
                                    initial logical part -}
               -> Named Axiom -- ^ goal to print
               -> [String] -- ^ extra options
               -> IO String -- ^ formatted output of the goal
showOWLProblem thName pst nGoal _ =
  let namedSens = initialState $ problemProverState
                    $ genFactProblemS thName pst Nothing
      sign = ontologySign $ problemProverState
                    $ genFactProblemS thName pst Nothing
  in return $ show (printOWLBasicTheory (sign, filter isAxiom namedSens))
       ++ "\n\nEntailments:\n\n" ++ show (printOWLBasicTheory (sign, [nGoal]))

{- |
   Invocation of the Fact Prover.
-}
runFact :: FactProverState
          {- ^ logical part containing the input Sign and axioms and possibly
          goals that have been proved earlier as additional axioms -}
          -> GenericConfig ProofTree -- ^ configuration to use
          -> Bool -- ^ True means save TPTP file
          -> String -- ^ name of the theory in the DevGraph
          -> Named Axiom -- ^ goal to prove
          -> IO (ATPRetval, GenericConfig ProofTree)
          -- ^ (retval, configuration with proof status and complete output)
runFact sps cfg saveFact thName nGoal = do
      let prob = showOWLProblemS thName sps []
          entail = showOWLProblemS thName
                     (sps { initialState = [ nGoal {isAxiom = True } ] }) []
          jar = "OWLFactProver.jar"
      when saveFact $ do
        writeFile tmpFileName prob
        writeFile (tmpFileName ++ ".entail.owl") entail
      (progTh, toolPath) <- check4HetsOWLjar jar
      if progTh then withinDirectory toolPath $ do
          tempDir <- getTemporaryDirectory
          timeTmpFile <- writeTempFile prob tempDir tmpFileName
          let entailsFile = timeTmpFile ++ ".entail.owl"
              command = "java -Djava.library.path=lib/native/`uname -m` -jar "
                ++ jar ++ " file://" ++ timeTmpFile ++ " file://" ++ entailsFile
          writeFile entailsFile entail
          t_start <- getHetsTime
          (mExit, outh, errh) <- timeoutCommand tLimit command
          t_end <- getHetsTime
          let t_u = diffHetsTime t_end t_start
          ((err, retval), output, tUsed) <- case mExit of
            Just ex -> do
              output <- hGetContents outh
              eOut <- hGetContents errh
              let outp = lines $ output ++ eOut
              return (proofStat ex simpleOptions outp t_u, outp, t_u)
            Nothing -> return
              ( (ATPTLimitExceeded, defaultProofStatus simpleOptions)
              , [], t_u)
          removeFile timeTmpFile
          removeFile entailsFile
          return (err, cfg
            { proofStatus = retval
            , resultOutput = output
            , timeUsed = tUsed
            })
        else return (ATPError "OWLFactProver not found", cfg)
  where
    simpleOptions = extraOpts cfg
    tLimit = fromMaybe 800 $ timeLimit cfg
    goalSuffix = '_' : senAttr nGoal
    tmpFileName = basename thName ++ goalSuffix ++ ".owl"
    proofStat exitCode options out tUsed = case exitCode of
      ExitFailure 10 -> (ATPSuccess, (provedStatus options tUsed)
                       { usedAxioms = map senAttr $ initialState sps })
      ExitFailure 20 -> (ATPSuccess, disProvedStatus options)
      ExitFailure _ -> ( ATPError (unlines ("Internal error." : out))
                       , defaultProofStatus options)
      ExitSuccess -> ( ATPError (unlines ("Internal error." : out))
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
                  , proofTree = emptyProofTree
                  , usedTime = ut
                  , tacticScript = tScript opts }
