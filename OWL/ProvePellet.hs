{- |
Module      :  $Header$
Description :  Interface to the OWL Ontology prover via Pellet.
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the Pellet service, uses GUI.GenericATP.
See <http://www.w3.org/2004/OWL/> for details on OWL, and
<http://pellet.owldl.com/> for Pellet (version 2.0.0-rc6)
-}

module OWL.ProvePellet (pelletProver, pelletConsChecker) where

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
import Common.Result as Result
import Common.Utils

import Data.List (isPrefixOf)
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime (..), secondsToDiffTime, getCurrentTime)

import System.Exit
import System.IO
import System.Directory
import System.Process

import Control.Monad (when)
import Control.Concurrent

data PelletProverState = PelletProverState
                           { ontologySign :: Sign
                           , initialState :: [Named Axiom]
                           } deriving (Show)

-- * Prover implementation
pelletProverState :: Sign
                  -> [Named Axiom]
                  -> [FreeDefMorphism Axiom OWLMorphism]
                  -- ^ freeness constraints
                  -> PelletProverState
pelletProverState sig oSens _ = PelletProverState
  { ontologySign = sig
  , initialState = filter isAxiom oSens }

pelletS :: String
pelletS = "Pellet"

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
pelletProver :: Prover Sign Axiom OWLMorphism OWLSub ProofTree
pelletProver = mkAutomaticProver pelletS sl_top pelletGUI
  pelletCMDLautomaticBatch

pelletConsChecker :: ConsChecker Sign Axiom OWLSub OWLMorphism ProofTree
pelletConsChecker = mkConsChecker pelletS sl_top consCheck

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Axiom OWLMorphism ProofTree PelletProverState
atpFun _ = ATPFunctions
  { initialProverState = pelletProverState
  , atpTransSenName = id   -- transSenName,
  , atpInsertSentence = insertOWLAxiom
  , goalOutput = \ a b _ -> showOWLProblem a b
  , proverHelpText = "http://clarkparsia.com/pellet/\n"
  , batchTimeEnv = "HETS_Pellet_BATCH_TIME_LIMIT"
  , fileExtensions = FileExtensions { problemOutput = ".owl"  -- owl-hets
                                    , proverOutput = ".pellet"
                                    , theoryConfiguration = ".pconf" }
  , runProver = runPellet
  , createProverOptions = extraOpts }

{- |
  Inserts a named OWL axiom into pellet prover state.
-}
insertOWLAxiom :: PelletProverState -- ^ prover state containing
                                    -- initial logical part
               -> Named Axiom -- ^ goal to add
               -> PelletProverState
insertOWLAxiom pps s = pps { initialState = initialState pps ++ [s] }

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}
pelletGUI :: String -- ^ theory name
          -> Theory Sign Axiom ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO [ProofStatus ProofTree] -- ^ proof status for each goal
pelletGUI thName th freedefs =
  genericATPgui (atpFun thName) True pelletS thName th
                freedefs emptyProofTree

-- ** command line function

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Pellet prover via MathServe.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomaticBatch ::
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
        -- snd: MVar to wait for the end of the thread
pelletCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                         thName defTS th freedefs =
  genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
    resultMVar pelletS thName
    (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions
{- |
  Runs the Pellet service.
-}

consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName _ tm freedefs = case tTarget tm of
  Theory sig nSens -> do
    let proverStateI = pelletProverState sig (toNamedList nSens) freedefs
        problemS = showOWLProblemS proverStateI
        tmpFileName = basename thName
        pStatus out tUsed = CCStatus
          { ccResult = Nothing
          , ccProofTree = ProofTree $ unlines out ++ "\n\n" ++ problemS
          , ccUsedTime = timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed }
        proofStatM :: ExitCode -> [String] -> Int -> CCStatus ProofTree
        proofStatM exitCode out tUsed = case exitCode of
          ExitSuccess ->   -- consistent
            (pStatus out tUsed) { ccResult = Just True }
          ExitFailure 1 -> -- not consistent
            (pStatus out tUsed) { ccResult = Just False }
          ExitFailure 2 -> -- error by runing pellet
            (pStatus out tUsed) { ccProofTree = ProofTree "Cannot run pellet." }
          ExitFailure 3 -> -- timeout
            (pStatus out tUsed)
            { ccProofTree = ProofTree $ unlines out ++ "\n\ntimeout" }
          ExitFailure 4 -> -- error by runing pellet
            (pStatus out tUsed) { ccProofTree = ProofTree
            $ "Pellet returned an error.\n" ++ unlines out }
          ExitFailure _ -> -- another errors
            pStatus out tUsed
    (progTh, pPath) <- check4Pellet
    if progTh then do
        t <- getCurrentTime
        tempDir <- getTemporaryDirectory
        let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                                  ++ "-" ++ show (utctDayTime t) ++ ".owl"
            command = "sh pellet.sh consistency file://" ++ timeTmpFile
        writeFile timeTmpFile problemS
        setCurrentDirectory pPath
        (_, outh, errh, proch) <- runInteractiveCommand command
        waitForProcess proch
        outp <- hGetContents outh
        eOut <- hGetContents errh
        let (exCode, output, tUsed) = analyseOutput outp eOut
        removeFile timeTmpFile
        return $ proofStatM exCode output tUsed
      else return $ pStatus ["Pellet not found"] (0 :: Int)

check4Pellet :: IO (Bool, FilePath)
check4Pellet = do
  pPath <- getEnvDef "PELLET_PATH" ""
  progTh <- doesFileExist $ pPath ++ "/pellet.sh"
  return (progTh, pPath)

-- TODO: Pellet Prove for single goals.
runPellet :: PelletProverState
          -- ^ logical part containing the input Sign and axioms and possibly
          -- goals that have been proved earlier as additional axioms
          -> GenericConfig ProofTree -- ^ configuration to use
          -> Bool -- ^ True means save TPTP file
          -> String -- ^ name of the theory in the DevGraph
          -> Named Axiom -- ^ goal to prove
          -> IO (ATPRetval, GenericConfig ProofTree)
          -- ^ (retval, configuration with proof status and complete output)
runPellet sps cfg savePellet thName nGoal = do
  let simpleOptions = extraOpts cfg
      tLimit = fromMaybe 800 $ timeLimit cfg
      extraOptions = "entail -e "
      goalSuffix = '_' : senAttr nGoal
      tmpFileName = basename thName ++ goalSuffix
      proofStat exitCode options out tUsed = case exitCode of
        ExitSuccess -> (ATPSuccess, (provedStatus options tUsed)
                       { usedAxioms = map senAttr $ initialState sps })
        ExitFailure 2 -> ( ATPError (unlines ("Internal error." : out))
                       , defaultProofStatus options)
        ExitFailure 112 -> (ATPTLimitExceeded, defaultProofStatus options)
        ExitFailure 105 -> (ATPBatchStopped, defaultProofStatus options)
        ExitFailure _ -> (ATPSuccess, disProvedStatus options)
      tScript opts = TacticScript $ show ATPTacticScript
                     { tsTimeLimit = configTimeLimit cfg
                     , tsExtraOpts = opts }
      defaultProofStatus opts =
        (openProofStatus (senAttr nGoal) pelletS emptyProofTree)
        { tacticScript = tScript opts }
      disProvedStatus opts = (defaultProofStatus opts) {goalStatus = Disproved}
      provedStatus opts ut = ProofStatus
                  { goalName = senAttr nGoal
                  , goalStatus = Proved True
                  , usedAxioms = []
                  , usedProver = pelletS
                  , proofTree = emptyProofTree
                  , usedTime =
                      timeToTimeOfDay $ secondsToDiffTime $ toInteger ut
                  , tacticScript = tScript opts }
  (progTh, pPath) <- check4Pellet
  if progTh then do
      let prob = showOWLProblemS sps
          entail = showOWLProblemS
                     sps { initialState = [ nGoal {isAxiom = True } ] }
      when savePellet $ do
        writeFile (tmpFileName ++ ".owl") prob
        writeFile (tmpFileName ++ ".entail.owl") entail
      t <- getCurrentTime
      tempDir <- getTemporaryDirectory
      let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                                ++ "-" ++ show (utctDayTime t) ++ ".owl"
          entailsFile = tempDir ++ "/" ++ tmpFileName ++ show (utctDay t)
                          ++ "-" ++ show (utctDayTime t) ++ ".entails.owl"
      writeFile timeTmpFile prob
      writeFile entailsFile entail
      let command = "sh pellet.sh " ++ extraOptions ++ " " ++ entailsFile
                      ++ " file://" ++ timeTmpFile
      setCurrentDirectory pPath
      (mExit, outh, errh) <- timeoutCommand tLimit command
      ((err, retval), output, tUsed) <- if isJust mExit then do
        output <- hGetContents outh
        eOut <- hGetContents errh
        let (exCode, outp, tUsed) = analyseOutput output eOut
        return (proofStat exCode simpleOptions outp tUsed, outp, tUsed)
        else return
          ((ATPTLimitExceeded, defaultProofStatus simpleOptions), [], tLimit)
      removeFile timeTmpFile
      removeFile entailsFile
      return (err, cfg { proofStatus = retval
                       , resultOutput = output
                       , timeUsed =
                           timeToTimeOfDay $ secondsToDiffTime $ toInteger tUsed
                       })
    else return
      ( ATPError "Could not find pellet prover. Is $PELLET_PATH set?"
      , emptyConfig pelletS (senAttr nGoal) emptyProofTree)

analyseOutput :: String -> String -> (ExitCode, [String], Int)
analyseOutput err outp =
  let errL = lines err
      outL = lines outp
      anaHelp x [] = x
      anaHelp (exCode, output, to) (line : ls) =
        let (okey, ovalue) = span (/= ':') line in
        if "Usage: java Pellet" `isPrefixOf` line
          -- error by running pellet.
          then (ExitFailure 2, output ++ [line], to)
          else if okey == "Consistent"    -- consistent state
            then if tail (tail ovalue) == "Yes" then
              anaHelp (ExitSuccess, output ++ [line], to) ls
              else anaHelp (ExitFailure 1, output ++ [line], to) ls
            else if "Time" `isPrefixOf` okey  -- get cup time
              then anaHelp (exCode, output ++ [line],
                     read $ fst $ span (/= ' ') $ tail ovalue :: Int) ls
              else if "All axioms are entailed" `isPrefixOf` line
                then anaHelp (ExitSuccess, output ++ [line], to) ls
                else if "Non-entailments:" `isPrefixOf` line
                  then anaHelp (ExitFailure 5, output ++ [line], to) ls
                  else if "ERROR:" `isPrefixOf` line
                    then anaHelp (ExitFailure 4, output ++ [line], to) ls
                    else anaHelp (exCode, output ++ [line], to) ls
  in anaHelp (ExitFailure 1, [], -1) (outL ++ errL)

showOWLProblemS :: PelletProverState -- ^ prover state containing
                                     -- initial logical part
                -> String -- ^ formatted output of the goal
showOWLProblemS pst =
    let namedSens = initialState $ genPelletProblemS pst Nothing
        sign = ontologySign $ genPelletProblemS pst Nothing
    in show $ printOWLBasicTheory (sign, filter isAxiom namedSens)

{- |
  Pretty printing OWL goal for pellet.
-}
showOWLProblem :: PelletProverState -- ^ prover state containing
                                    -- initial logical part
               -> Named Axiom -- ^ goal to print
               -> IO String -- ^ formatted output of the goal
showOWLProblem pst nGoal =
  let sign = ontologySign $ genPelletProblemS pst Nothing
  in return $ showOWLProblemS pst
       ++ "\n\nEntailments:\n\n" ++ show (printOWLBasicTheory (sign, [nGoal]))

{- |
  Generate an OWL problem.
-}
genPelletProblemS :: PelletProverState
                  -> Maybe (Named Axiom)
                  -> PelletProverState
genPelletProblemS pps m_nGoal =
    pps { initialState = initialState pps ++ maybeToList m_nGoal }
