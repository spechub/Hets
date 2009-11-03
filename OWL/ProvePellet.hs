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
<http://pellet.owldl.com/> for Pellet.
-}

module OWL.ProvePellet (pelletProver,pelletGUI,pelletCMDLautomatic,
                           pelletCMDLautomaticBatch,
                           pelletConsChecker) where

import Logic.Prover

import OWL.AS
import OWL.Morphism
import OWL.Sign
import OWL.Print
import OWL.Sublogic

import GUI.GenericATP
import Interfaces.GenericATPState
import GUI.Utils (infoDialog)

import Proofs.BatchProcessing

import Common.AS_Annotation
import Common.ProofTree
import Common.Result as Result
import Common.Utils

import Data.List (isPrefixOf)
import Data.Maybe
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import qualified Control.Concurrent as Concurrent

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Monad (when)
import Control.Concurrent

data PelletProverState = PelletProverState
                        { ontologySign :: Sign
                        , initialState :: [Named Axiom] }
                         deriving (Show)
data PelletProblem = PelletProblem
                   { identifier :: PelletID
                   -- , description :: Description
                   , problemProverState :: PelletProverState
                   -- , settings :: [PelletSetting]
                   } deriving (Show)
type PelletID = String

{-
data PelletSetting = PelletSetting
                   { settingName :: String
                   , settingValue :: [String]
                   } deriving (Show)
-}

-- * Prover implementation
pelletProverState :: Sign
                 -> [Named Axiom]
                 -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
                 -> PelletProverState
pelletProverState sig oSens _ = PelletProverState
         { ontologySign = sig
         , initialState = filter isAxiom oSens }

{- |
  The Prover implementation. First runs the batch prover (with graphical feedback), then starts the GUI prover.
-}
pelletProver :: Prover Sign Axiom OWLMorphism OWLSub ProofTree
pelletProver = (mkProverTemplate "Pellet" sl_top pelletGUI)
    { proveCMDLautomatic = Just pelletCMDLautomatic
    , proveCMDLautomaticBatch = Just pelletCMDLautomaticBatch }

pelletConsChecker :: ConsChecker Sign Axiom OWLSub OWLMorphism ProofTree
pelletConsChecker = (mkConsChecker "Pellet" sl_top consCheck)
  { ccNeedsTimer = False }


{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Axiom OWLMorphism ProofTree PelletProverState
atpFun thName = ATPFunctions
    { initialProverState = pelletProverState,
      atpTransSenName = id,   -- transSenName,
      atpInsertSentence = insertOWLAxiom,
      goalOutput = showOWLProblem thName,
      proverHelpText = "http://clarkparsia.com/pellet/\n",
      batchTimeEnv = "HETS_Pellet_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".owl",  -- owl-hets
                                      proverOutput = ".pellet",
                                      theoryConfiguration = ".pconf"},
      runProver = runPellet,
      createProverOptions = extraOpts}

{- |
  Inserts a named OWL axiom into pellet prover state.
-}
insertOWLAxiom :: PelletProverState -- ^ prover state containing
                                      --   initial logical part
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
           -> IO([ProofStatus ProofTree]) -- ^ proof status for each goal
pelletGUI thName th freedefs =
    genericATPgui (atpFun thName) True (proverName pelletProver) thName th
                  freedefs emptyProofTree

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomatic ::
           String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Axiom ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
        -> IO (Result.Result ([ProofStatus ProofTree]))
           -- ^ Proof status for goals and lemmas
pelletCMDLautomatic thName defTS th freedefs =
    genericCMDLautomatic (atpFun thName) (proverName pelletProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Pellet prover via MathServe.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [ProofStatus ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> TacticScript -- ^ default tactic script
        -> Theory Sign Axiom ProofTree -- ^ theory
        -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
pelletCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (proverName pelletProver) thName
        (parseTacticScript batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions
{- |
  Runs the Pellet service.
-}

getEnvSec :: String -> IO String
getEnvSec s = getEnvDef s ""

consCheck :: String
          -> TacticScript
          -> TheoryMorphism Sign Axiom OWLMorphism ProofTree
          -> [FreeDefMorphism Axiom OWLMorphism] -- ^ freeness constraints
          -> IO (CCStatus ProofTree)
consCheck thName (TacticScript tl) tm freedefs =
    case tTarget tm of
      Theory sig nSens ->
        let
          saveOWL = False
          timeLimitI = fromMaybe 800 $ readMaybe tl
          proverStateI = pelletProverState sig
                                       (toNamedList nSens) freedefs
          problemS     = showOWLProblemS thName proverStateI []
          simpleOptions = "consistency "
          extraOptions  = ""
          saveFileName  = reverse $ fst $ span (/='/') $ reverse thName
          tmpFileName   = saveFileName
          pStatus out tUsed = CCStatus
            { ccResult = Nothing
            , ccProofTree = ProofTree $ unlines out ++ "\n\n" ++ problemS
            , ccUsedTime = timeToTimeOfDay
                $ secondsToDiffTime $ toInteger tUsed }
          proofStatM :: ExitCode -> String ->  [String]
                     -> Int -> CCStatus ProofTree
          proofStatM exitCode _ out tUsed =
              case exitCode of
                ExitSuccess ->   -- consistent
                    (pStatus out tUsed)
                    { ccResult = Just True }
                ExitFailure 1 ->   -- not consistent
                    (pStatus out tUsed)
                    { ccResult = Just False }
                ExitFailure 2 ->   -- error by runing pellet
                    (pStatus out tUsed)
                    { ccProofTree = ProofTree "Cannot run pellet." }
                ExitFailure 3 ->  -- timeout
                    (pStatus out tUsed)
                    { ccProofTree = ProofTree $ unlines out ++ "\n\n"
                                    ++ "timeout" }
                ExitFailure 4 ->   -- error by runing pellet
                    (pStatus out tUsed)
                    { ccProofTree = ProofTree $ "Pellet returned an error.\n"
                        ++ unlines out }
                ExitFailure _ ->    -- another errors
                    pStatus out tUsed

          timeWatch :: Int -> IO (CCStatus ProofTree) -> IO (CCStatus ProofTree)
          timeWatch time process =
              do
                mvar <- newEmptyMVar
                tid1 <- forkIO $ do z <- process
                                    putMVar mvar (Just z)
                tid2 <- forkIO $ do threadDelay (time * 1000000)
                                    putMVar mvar Nothing
                res <- takeMVar mvar
                case res of
                  Just z -> do
                           killThread tid2 `catch` print
                           return z
                  Nothing -> do
                           killThread tid1 `catch` print
                           return $ pStatus ["timeout"] time
        in
          do
              (progTh, progEx) <- check4Pellet
              case (progTh, progEx) of
                (True,True) -> do
                   when saveOWL
                          (writeFile (saveFileName ++".owl") problemS)
                   t <- getCurrentTime
                   tempDir <- getTemporaryDirectory
                   let timeTmpFile = tempDir ++ "/" ++ tmpFileName
                                     ++ (show $ utctDay t) ++
                                     "-" ++ (show $ utctDayTime t) ++ ".owl"
                       tmpURI = "file://" ++ timeTmpFile
                   writeFile timeTmpFile $ problemS
                   let command = "sh pellet.sh "
                                 ++ simpleOptions ++ extraOptions
                                 ++ tmpURI
                   pPath     <- getEnvSec "PELLET_PATH"
                   setCurrentDirectory(pPath)
                   outState <- timeWatch timeLimitI $
                     (do
                       (_, outh, errh, proch) <- runInteractiveCommand command
                       waitForProcess proch
                       outp  <- hGetContents outh
                       eOut    <- hGetContents errh
                       let (exCode, output, tUsed) = analyseOutput outp eOut
                       let outState = proofStatM exCode simpleOptions
                                              output tUsed
                       return outState
                     )
                   removeFile timeTmpFile
                   return outState
                (b, _) -> do
                   let mess = "Pellet not " ++
                         if b then "executable" else "found"
                   infoDialog "Pellet prover" mess
                   return $ pStatus [mess] (0 :: Int)

check4Pellet :: IO (Bool, Bool)
check4Pellet =
    do
      pPath     <- getEnvSec "PELLET_PATH"
      progTh    <- doesFileExist $ pPath ++ "/pellet.sh"
      progEx <- if (progTh)
                 then
                     do
                       progPerms <- getPermissions $ pPath ++ "/pellet.sh"
                       return $ executable $ progPerms
                 else
                     return False
      return $ (progTh, progEx)

-- TODO: Pellet Prove for single goals.
runPellet :: PelletProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> Named Axiom -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runPellet sps cfg savePellet thName nGoal =
    do
      (progTh, progEx) <- check4Pellet
      case (progTh,progEx) of
        (True,True) -> do
          let prob   = showOWLProblemS thName sps []
          let entail = showOWLProblemS thName
                  (sps{initialState = [nGoal{isAxiom=True}]}) []
          when savePellet
            (writeFile (saveFileName ++".owl") prob)
          when savePellet
            (writeFile (saveFileName ++".entail.owl") entail)
          t <- getCurrentTime
          tempDir <- getTemporaryDirectory
          let timeTmpFile = tempDir ++ "/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".owl"
              entailsFile = tempDir ++ "/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".entails.owl"
          writeFile timeTmpFile prob
          writeFile entailsFile entail
          let command = "sh pellet.sh " ++ extraOptions ++ " " ++ entailsFile
                        ++ " " ++ timeTmpFile
          pPath     <- getEnvSec "PELLET_PATH"
          setCurrentDirectory(pPath)
          ((err, retval),output, tUsed) <- case tLimit of
            Nothing ->
                do
                  (_, outh, errh, proch) <- runInteractiveCommand command
                  waitForProcess proch
                  output  <- hGetContents outh
                  eOut    <- hGetContents errh
                  let (exCode, outp, tUsed) = analyseOutput output eOut
                  return $ (proofStat exCode simpleOptions outp tUsed,
                            outp, tUsed)
            Just tm  ->
                timeWatchP tm
                  (do
                    (_, outh, errh, proch) <- runInteractiveCommand command
                    waitForProcess proch
                    output  <- hGetContents outh
                    eOut    <- hGetContents errh
                    let (exCode, outp, tUsed) = analyseOutput output eOut
                    return $ (proofStat exCode simpleOptions outp tUsed,
                            outp, tUsed)
                    )
          removeFile timeTmpFile
          removeFile entailsFile
          return (err,
                  cfg{proofStatus = retval,
                      resultOutput = output,
                      timeUsed     = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger tUsed})
        (True,False) -> return
            (ATPError "Pellet prover found, but file is not executable.",
                  emptyConfig (proverName pelletProver)
                              (senAttr nGoal) emptyProofTree)
        (False,_) -> return
            (ATPError "Could not find pellet prover. Is $PELLET_PATH set?",
                  emptyConfig (proverName pelletProver)
                              (senAttr nGoal) emptyProofTree)

  where
    simpleOptions = extraOpts cfg
    tLimit        = timeLimit cfg
    extraOptions  = "entail -e "
    goalSuffix    = '_' : senAttr nGoal
    saveFileName  = thName ++ goalSuffix
    tmpFileName   = reverse (takeWhile (/= '/') $ reverse thName) ++ goalSuffix

    timeWatchP :: Int -> IO ((ATPRetval, ProofStatus ProofTree), [String], Int)
                     -> IO ((ATPRetval, ProofStatus ProofTree), [String] , Int)
    timeWatchP time process =
        do
          mvar <- newEmptyMVar
          tid1 <- forkIO $ do z <- process
                              putMVar mvar (Just z)
          tid2 <- forkIO $ do threadDelay (time * 1000000)
                              putMVar mvar Nothing
          res <- takeMVar mvar
          case res of
            Just z -> do
                     killThread tid2 `catch` (\e -> putStrLn (show e))
                     return z
            Nothing -> do
                     killThread tid1 `catch` (\e -> putStrLn (show e))
                     return ((ATPTLimitExceeded
                            , defaultProofStatus simpleOptions)
                            , [],time)

    proofStat exitCode options out tUsed =
            case exitCode of
              ExitSuccess -> (ATPSuccess, (provedStatus options tUsed)
                                        {
                                          usedAxioms = map senAttr $
                                                       initialState sps
                                        }
                             )
              ExitFailure 2 -> (ATPError (unlines ("Internal error.":out)),
                                defaultProofStatus options)
              ExitFailure 112 ->
                       (ATPTLimitExceeded, defaultProofStatus options)
              ExitFailure 105 ->
                       (ATPBatchStopped, defaultProofStatus options)
              ExitFailure _ ->
                  (ATPSuccess, disProvedStatus options)
    tScript opts = TacticScript $ show $ ATPTacticScript
                        { tsTimeLimit = configTimeLimit cfg
                        , tsExtraOpts = opts }
    defaultProofStatus opts =
            (openProofStatus
            (senAttr nGoal) (proverName pelletProver) $
                                    emptyProofTree)
                       { tacticScript = tScript opts }

    disProvedStatus opts = (defaultProofStatus opts)
                               {goalStatus = Disproved}

    provedStatus opts ut =
        ProofStatus {
               goalName = senAttr nGoal
              ,goalStatus = Proved (Just True)
              ,usedAxioms = getAxioms -- []
              ,usedProver = proverName pelletProver
              ,proofTree =  emptyProofTree
              ,usedTime = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger ut
              ,tacticScript = tScript opts }

    getAxioms = []

analyseOutput :: String -> String -> (ExitCode, [String], Int)
analyseOutput err outp =
    let
        errL = lines err
        outL = lines outp
        anaHelp x [] = x
        anaHelp (exCode, output, to) (line:ls) =
          let (okey, ovalue) = span (/=':') line
          in
          if "Usage: java Pellet" `isPrefixOf` line
             -- error by running pellet.
            then (ExitFailure 2, (output ++ [line]), to)
            else if okey == "Consistent"    -- consistent state
                   then if (tail $ tail ovalue) == "Yes" then
                           anaHelp (ExitSuccess, (output ++ [line]), to) ls
                          else anaHelp (ExitFailure 1, (output ++ [line]), to) ls
                   else if "Time" `isPrefixOf` okey  -- get cup time
                           then anaHelp (exCode, (output ++ [line]),
                           ((read $ fst $ span (/=' ') $ tail ovalue)::Int)) ls
                           else if "All axioms are entailed" `isPrefixOf` line
                                then
                                    anaHelp (ExitSuccess, (output ++ [line]), to) ls
                                else if "Non-entailments:" `isPrefixOf` line
                                     then
                                           anaHelp (ExitFailure 5, (output ++ [line]), to) ls
                                     else if "ERROR:" `isPrefixOf` line
                                          then
                                              anaHelp (ExitFailure 4, (output ++ [line]), to) ls
                                          else
                                              anaHelp (exCode, (output ++ [line]), to) ls
    in
      anaHelp (ExitFailure 1, [], -1) (outL ++ errL)

showOWLProblemS ::  String -- ^ theory name
               -> PelletProverState -- ^ prover state containing
                                    -- initial logical part
               -> [String] -- ^ extra options
               -> String -- ^ formatted output of the goal
showOWLProblemS thName pst _ =
    let namedSens = initialState $ problemProverState
                    $ genPelletProblemS thName pst Nothing
        sign      = ontologySign $ problemProverState
                    $ genPelletProblemS thName pst Nothing
    in show $ printOWLBasicTheory (sign, filter (\ax -> isAxiom(ax)) namedSens)

{- |
  Pretty printing SoftFOL goal in DFG format.
-}
showOWLProblem :: String -- ^ theory name
               -> PelletProverState -- ^ prover state containing
                                    -- initial logical part
               -> Named Axiom -- ^ goal to print
               -> [String] -- ^ extra options
               -> IO String -- ^ formatted output of the goal
showOWLProblem thName pst nGoal _ =
    let namedSens = initialState $ problemProverState
                    $ genPelletProblemS thName pst Nothing
        sign      = ontologySign $ problemProverState
                    $ genPelletProblemS thName pst Nothing
    in return $
       ((show $ printOWLBasicTheory (sign, filter (\ax -> isAxiom(ax)) namedSens))
        ++ "\n\nEntailments:\n\n" ++
        (show $ printOWLBasicTheory (sign, [nGoal]))
       )

{- |
  Generate a SoftFOL problem with time stamp while maybe adding a goal.
-}
genPelletProblemS :: String -> PelletProverState
                -> Maybe (Named Axiom)
                -> PelletProblem
genPelletProblemS thName pps m_nGoal =
       PelletProblem
        {identifier = thName
        , problemProverState = pps
                        { initialState = initialState pps ++
                                         (maybe [] (\g -> g:[]) m_nGoal)}
         }
