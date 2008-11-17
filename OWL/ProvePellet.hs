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

import Common.AS_Annotation

import OWL.Sign
import OWL.Print

import HTk

import GUI.GenericATP
import GUI.GenericATPState
import GUI.HTkUtils

import Proofs.BatchProcessing

import qualified Common.AS_Annotation as AS_Anno
import Common.DefaultMorphism
import Common.ProofTree
import qualified Common.Result as Result

import Data.List (isPrefixOf)
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import qualified Control.Concurrent as Concurrent

import System
import System.IO
import System.Process
import System.Directory
import System.Environment

import Control.Concurrent
import Control.Concurrent.MVar

import Common.Utils
data PelletProverState = PelletProverState
                        { ontologySign :: Sign
                        , initialState :: [AS_Anno.Named Sentence] }
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
                 -> [AS_Anno.Named Sentence]
                 -> [FreeDefMorphism (DefaultMorphism Sign)] -- ^ freeness constraints
                 -> PelletProverState
pelletProverState sig oSens _ = PelletProverState
         { ontologySign = sig
          ,initialState = filter AS_Anno.isAxiom oSens }

{- |
  The Prover implementation. First runs the batch prover (with graphical feedback), then starts the GUI prover.
-}
pelletProver :: Prover Sign Sentence (DefaultMorphism Sign) () ProofTree
pelletProver = (mkProverTemplate "Pellet" () pelletGUI)
    { proveCMDLautomatic = Just pelletCMDLautomatic
    , proveCMDLautomaticBatch = Just pelletCMDLautomaticBatch }

pelletConsChecker :: ConsChecker Sign Sentence () (DefaultMorphism Sign) ProofTree
pelletConsChecker = mkProverTemplate "Pellet Consistency Checker" () consCheck


{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Sentence (DefaultMorphism Sign) ProofTree PelletProverState
atpFun thName = ATPFunctions
    { initialProverState = pelletProverState,
      atpTransSenName = id,   -- transSenName,
      atpInsertSentence = insertOWLSentence,
      goalOutput = showOWLProblem thName,
      proverHelpText = "http://clarkparsia.com/pellet/\n",
      batchTimeEnv = "HETS_Pellet_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".owl",  -- owl-hets
                                      proverOutput = ".pellet",
                                      theoryConfiguration = ".pconf"},
      runProver = runPellet,
      createProverOptions = extraOpts}

{- |
  Inserts a named SoftFOL term into SoftFOL prover state.
-}
insertOWLSentence :: PelletProverState -- ^ prover state containing
                                      --   initial logical part
                  -> AS_Anno.Named Sentence -- ^ goal to add
                  -> PelletProverState
insertOWLSentence pps s =
    pps{initialState = (initialState pps) ++ [s]}

-- ** GUI

{- |
  Invokes the generic prover GUI.
-}
pelletGUI :: String -- ^ theory name
           -> Theory Sign Sentence ProofTree
           -> [FreeDefMorphism (DefaultMorphism Sign)] -- ^ freeness constraints
           -> IO([Proof_status ProofTree]) -- ^ proof status for each goal
pelletGUI thName th freedefs =
    genericATPgui (atpFun thName) True (prover_name pelletProver) thName th
                  freedefs emptyProofTree

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> [FreeDefMorphism (DefaultMorphism Sign)] -- ^ freeness constraints
        -> IO (Result.Result ([Proof_status ProofTree]))
           -- ^ Proof status for goals and lemmas
pelletCMDLautomatic thName defTS th freedefs =
    genericCMDLautomatic (atpFun thName) (prover_name pelletProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th freedefs emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Pellet prover via MathServe.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> [FreeDefMorphism (DefaultMorphism Sign)] -- ^ freeness constraints
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
pelletCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th freedefs =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name pelletProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th freedefs emptyProofTree

-- * Main prover functions
{- |
  Runs the Pellet service.
-}

spamOutput :: Proof_status ProofTree -> IO ()
spamOutput ps =
    let
        dName = goalName ps
        dStat = goalStatus ps
        dTree = proofTree ps
    in
      case dStat of
        Open -> createTextSaveDisplay "Pellet prover" ("./"++ dName ++".pellet.log")
                (
                 "I was not able to find a model for the goal " ++
                 dName ++". :( \n" ++
                 show dTree
                )
        Disproved -> createTextSaveDisplay "Pellet prover" (dName ++".pellet.owl")
                (
                 "Your theory " ++
                 dName ++" has no model. :( \n" ++
                 show dTree
                )
        Proved (Just True) ->     -- consistent
             do --createInfoWindow "Pellet consistency check"
                --                     "This ontology is consistent."
                createTextSaveDisplay "Pellet prover" ("./"++ dName ++".pellet.log")
                 (
                 -- "I found a model for the theory " ++
                 -- dName ++". :) \n" ++
                 show dTree
                 )

        Proved (Just False) ->   -- not consistent
             do --createInfoWindow "Pellet consistency check"
                --                     "This ontology is not consistent."
                createTextSaveDisplay "Pellet prover" ("./"++ dName ++".pellet.log")
                 (
                 -- "I found a model for the theory " ++
                 -- dName ++". :) \n" ++
                 show dTree
                 )

        Proved Nothing -> return ()  -- todo: another errors

getEnvSec :: String -> IO [Char]
getEnvSec s =
    do
      env <- getEnvironment
      let var = filter (\(z,_) -> z == s) env
      case length var of
        0 -> return ""
        1 -> return $ snd $ head $ var
        _ -> fail $ "Ambigoous environment"

consCheck :: String
          -> TheoryMorphism Sign Sentence (DefaultMorphism Sign) ProofTree
          -> [FreeDefMorphism (DefaultMorphism Sign)] -- ^ freeness constraints
          -> IO([Proof_status ProofTree])
consCheck thName tm freedefs =
    case t_target tm of
      Theory sig nSens ->
        let
          saveOWL = False
          timeLimitI = 800
          tac      = Tactic_script $ show $ ATPTactic_script
                      {ts_timeLimit = timeLimitI,
                       ts_extraOpts = [extraOptions]
                      }
          proverStateI = pelletProverState sig
                                       (toNamedList nSens) freedefs
          -- problem     = showOWLProblemA thName proverStateI []
          problemS     = showOWLProblemS thName proverStateI []
          simpleOptions = "consistency "
          extraOptions  = ""
          saveFileName  = (reverse $ fst $ span (/='/') $ reverse thName)
          tmpFileName   = saveFileName

          runPelletRealM :: IO([Proof_status ProofTree])
          runPelletRealM = do
              pPath     <- getEnvSec "PELLET_PATH"
              progTh    <- doesFileExist $ pPath ++ "/pellet.sh"
              progEx <- if (progTh)
                         then
                             do
                               progPerms <- getPermissions $ pPath ++ "/pellet.sh"
                               return $ executable $ progPerms
                         else
                             return False
              case (progTh, progEx) of
                (True,True) -> do
                   when saveOWL
                          (writeFile (saveFileName ++".owl") problemS)
                   t <- getCurrentTime
                   let timeTmpFile = "/tmp/" ++ tmpFileName
                                     ++ (show $ utctDay t) ++
                                     "-" ++ (show $ utctDayTime t) ++ ".owl"
                       tmpURI = "file://"++timeTmpFile
                   writeFile timeTmpFile $ problemS
                   let command = "cd $PELLET_PATH; sh pellet.sh "
                                 ++ simpleOptions ++ extraOptions
                                 ++ tmpURI
                   outState <- timeWatch timeLimitI $
                     (do
                       (_, outh, errh, proch) <- runInteractiveCommand command
                       (exCode, output, tUsed) <- parsePelletOut outh errh proch
                       let outState = proof_statM exCode simpleOptions
                                              output tUsed
                       return outState
                     )
                   spamOutput outState
                   removeFile timeTmpFile
                   return [outState]
                (True,False) -> do
                   createInfoWindow "Pellet prover" "Pellet not executable"
                   return [Proof_status
                           {
                            goalName = thName
                           , goalStatus = Open
                           , usedAxioms = getAxioms
                           , proverName = (prover_name pelletProver)
                           , proofTree  = ProofTree "Pellet not executable"
                           , usedTime = timeToTimeOfDay $
                                        secondsToDiffTime 0
                           ,tacticScript  = tac
                           }]
                (False,_) -> do
                   createInfoWindow "Pellet prover" "Pellet not found"
                   return [Proof_status
                           {
                            goalName = thName
                           , goalStatus = Open
                           , usedAxioms = getAxioms
                           , proverName = (prover_name pelletProver)
                           , proofTree  = ProofTree "Pellet not found"
                           , usedTime = timeToTimeOfDay $
                                        secondsToDiffTime 0
                           ,tacticScript  = tac
                           }]


          proof_statM :: ExitCode -> String ->  [String]
                      -> Int -> Proof_status ProofTree
          proof_statM exitCode _ out tUsed =
              case exitCode of
                ExitSuccess ->   -- consistent
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Proved (Just True)
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree = ProofTree (unlines out
                                      ++ "\n\n" ++ problemS)
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime $ toInteger tUsed
                    ,tacticScript  = tac
                    }
                ExitFailure 1 ->   -- not consistent
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Proved (Just False)
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree = ProofTree (unlines out
                                      ++ "\n\n" ++ (problemS))
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime $ toInteger tUsed
                    ,tacticScript  = tac
                    }
                ExitFailure 2 ->   -- error by runing pellet
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Disproved
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree = ProofTree "can not run pellet."
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime $ toInteger tUsed
                    ,tacticScript  = tac
                    }
                ExitFailure 3 ->  -- timeout
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Open
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree  = ProofTree (unlines out
                                      ++ "\n\n" ++ "timeout" ++
                                                    unlines out)
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime 0
                    ,tacticScript  = tac
                    }
                ExitFailure _ ->    -- another errors
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Disproved
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree =   ProofTree (unlines out
                                        ++ "\n\n" ++  (problemS))
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime $ toInteger tUsed
                    ,tacticScript  = tac
                    }

          getAxioms =
               map AS_Anno.senAttr $ initialState proverStateI

          timeWatch :: Int
                    -> IO (Proof_status ProofTree)
                    -> IO (Proof_status ProofTree)
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
                           killThread tid2 `catch` (\e -> putStrLn (show e))
                           return z
                  Nothing -> do
                           killThread tid1 `catch` (\e -> putStrLn (show e))
                           return (Proof_status{
                               goalName = thName
                             , goalStatus = Open
                             , usedAxioms = getAxioms
                             , proverName = (prover_name pelletProver)
                             , proofTree  = ProofTree ("\n\n" ++ "timeout")
                             ,usedTime = timeToTimeOfDay $
                               secondsToDiffTime 0
                             ,tacticScript  = tac
                             })
        in
          runPelletRealM

-- TODO: Pellet Prove for single goals.
runPellet :: PelletProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named Sentence -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runPellet sps cfg savePellet thName nGoal = do
  -- putStrLn ("running Pellet...")
  runPelletReal

  where
    simpleOptions = extraOpts cfg
    tLimit        = timeLimit cfg
    extraOptions  = "entail -e "
    saveFileName  = thName++'_':AS_Anno.senAttr nGoal
    tmpFileName   = (reverse $ fst $ span (/='/') $ reverse thName) ++
                       '_':AS_Anno.senAttr nGoal
    runPelletReal = do
      pPath     <- getEnvSec "PELLET_PATH"
      progTh    <- doesFileExist $ pPath ++ "/pellet.sh"
      progEx <- if (progTh)
                 then
                     do
                       progPerms <- getPermissions $ pPath ++ "/pellet.sh"
                       return $ executable $ progPerms
                 else
                     return False
      case (progTh,progEx) of
        (True,True) -> do
          let prob   = showOWLProblemS thName sps []
          let entail = showOWLProblemS thName (sps{initialState = [nGoal{isAxiom=True}]}) []
          when savePellet
            (writeFile (saveFileName ++".owl") prob)
          when savePellet
            (writeFile (saveFileName ++".entail.owl") entail)
          t <- getCurrentTime
          let timeTmpFile = "/tmp/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".owl"
              entailsFile = "/tmp/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".entails.owl"
          writeFile timeTmpFile prob
          writeFile entailsFile entail
          let command = "cd $PELLET_PATH; sh pellet.sh " ++ extraOptions ++ " " ++ entailsFile
                        ++ " " ++ timeTmpFile
          -- putStrLn command
          ((err, retval),output, tUsed) <- case tLimit of
            Nothing ->
                do
                  (_, outh, errh, proch) <- runInteractiveCommand command
                  (exCode, output, tUsed) <- parsePelletOut outh errh proch
                  return $ (proof_stat exCode simpleOptions output tUsed,
                            output, tUsed)
            Just tm  ->
                timeWatchP tm
                  (do
                    (_, outh, errh, proch) <- runInteractiveCommand command
                    (exCode, output, tUsed) <- parsePelletOut outh errh proch
                    return $ (proof_stat exCode simpleOptions output tUsed,
                            output, tUsed)
                    )
          removeFile timeTmpFile
          removeFile entailsFile
          return (err,
                  cfg{proof_status = retval,
                      resultOutput = output,
                      timeUsed     = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger tUsed})
        (True,False) -> return
            (ATPError "Pellet prover found, but file is not executable.",
                  emptyConfig (prover_name pelletProver)
                              (AS_Anno.senAttr nGoal) emptyProofTree)
        (False,_) -> return
            (ATPError "Could not find pellet prover. Is $PELLET_PATH set?",
                  emptyConfig (prover_name pelletProver)
                              (AS_Anno.senAttr nGoal) emptyProofTree)

    timeWatchP :: Int -> IO ((ATPRetval, Proof_status ProofTree), [String], Int)
                     -> IO ((ATPRetval, Proof_status ProofTree), [String] , Int)
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
                            , defaultProof_status simpleOptions)
                            , [],time)

    proof_stat exitCode options out tUsed =
            case exitCode of
              ExitSuccess -> (ATPSuccess, (proved_status options tUsed)
                                        {
                                          usedAxioms = map AS_Anno.senAttr $
                                                       initialState sps
                                        }
                             )
              ExitFailure 2 -> (ATPError (unlines ("Internal error.":out)),
                                defaultProof_status options)
              ExitFailure 112 ->
                       (ATPTLimitExceeded, defaultProof_status options)
              ExitFailure 105 ->
                       (ATPBatchStopped, defaultProof_status options)
              ExitFailure _ ->
                  (ATPSuccess, disProved_status options)

    defaultProof_status opts =
            (openProof_status
            (AS_Anno.senAttr nGoal) (prover_name pelletProver) $
                                    emptyProofTree)
                       {tacticScript = Tactic_script $ show $ ATPTactic_script
                        {ts_timeLimit = configTimeLimit cfg,
                         ts_extraOpts = opts} }

    disProved_status opts = (defaultProof_status opts)
                               {goalStatus = Disproved}

    proved_status opts ut =
        Proof_status{
               goalName = AS_Anno.senAttr nGoal
              ,goalStatus = Proved (Just True)
              ,usedAxioms = getAxioms -- []
              ,proverName = (prover_name pelletProver)
              ,proofTree =   emptyProofTree
              ,usedTime = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger ut
              ,tacticScript  = Tactic_script $ show $ ATPTactic_script
                               {ts_timeLimit = configTimeLimit cfg,
                                ts_extraOpts = opts}
                    }

    getAxioms = []

parsePelletOut :: Handle        -- ^ handel of stdout
               -> Handle        -- ^ handel of stderr
               -> ProcessHandle -- ^ handel of process
               -> IO (ExitCode, [String], Int)
                       -- ^ (exit code, complete output, used time)
parsePelletOut outh _ proc = do
    --pellet does not write to stderr here, so ignore output
    --err <- hGetLine errh
    --if null err then
  readLineAndParse (ExitFailure 1, [], -1)
  where
   readLineAndParse (exCode, output, to) = do
    -- putStrLn $ show exCode
    procState <- isProcessRun
    case procState of
     ExitSuccess -> do
      iseof <- hIsEOF outh
      if iseof then
          do -- ec <- isProcessRun proc
             -- putStrLn "eof"
             waitForProcess proc
             return (exCode, output, to)
        else do
          line <-hGetLine outh
          -- putStrLn $ show line
          let (okey, ovalue) = span (/=':') line
          if "Usage: java Pellet" `isPrefixOf` line
             -- error by running pellet.
            then do waitForProcess proc
                    return (ExitFailure 2, (output ++ [line]), to)
            else if okey == "Consistent"    -- consistent state
                   then if (tail $ tail ovalue) == "Yes" then
                           readLineAndParse (ExitSuccess, (output ++ [line]), to)
                          else readLineAndParse (ExitFailure 1, (output ++ [line]), to)
                   else if "Time" `isPrefixOf` okey  -- get cup time
                           then readLineAndParse (exCode, (output ++ [line]),
                           ((read $ fst $ span (/=' ') $ tail ovalue)::Int))
                           else if "All axioms are entailed" `isPrefixOf` line
                                then
                                    readLineAndParse (ExitSuccess, (output ++ [line]), to)
                                else if "Non-entailments:" `isPrefixOf` line
                                     then
                                         do
                                           readLineAndParse (ExitFailure 5, (output ++ [line]), to)
                                     else
                                         readLineAndParse
                                         (exCode, (output ++ [line]), to)

     failure -> do waitForProcess proc
                   return (failure, output, to)

    -- check if pellet running
   isProcessRun = do
      exitcode <- getProcessExitCode proc
      case exitcode of
        Nothing -> return ExitSuccess
        Just (ExitFailure i) -> return (ExitFailure i)
        Just ExitSuccess     -> return ExitSuccess

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
               -> AS_Anno.Named Sentence -- ^ goal to print
               -> [String] -- ^ extra options
               -> IO String -- ^ formatted output of the goal
showOWLProblem thName pst nGoal _ = do
  prob <- genPelletProblem thName pst (Just nGoal)
  return $ show (initialState $ problemProverState prob)

{- |
  Generate a SoftFOL problem with time stamp while maybe adding a goal.
-}
genPelletProblem :: String -> PelletProverState
                -> Maybe (AS_Anno.Named Sentence)
                -> IO PelletProblem
genPelletProblem thName pps m_nGoal = do
       return $ genPelletProblemS thName pps m_nGoal

{- |
  Generate a SoftFOL problem with time stamp while maybe adding a goal.
-}
genPelletProblemS :: String -> PelletProverState
                -> Maybe (AS_Anno.Named Sentence)
                -> PelletProblem
genPelletProblemS thName pps m_nGoal =
       PelletProblem
        {identifier = thName
        , problemProverState = pps
                        { initialState = initialState pps ++
                                         (maybe [] (\g -> g:[]) m_nGoal)}
--        , settings = []
         }

{- |
  Returns the time limit from GenericConfig if available. Otherwise
  guiDefaultTimeLimit is returned.
-}
configTimeLimit :: GenericConfig ProofTree
                -> Int
configTimeLimit cfg =
    maybe (guiDefaultTimeLimit) id $ timeLimit cfg

{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible. Otherwise a default
  prover's tactic script is returned.
-}
parseTactic_script :: Int -- ^ default time limit (standard:
                          -- 'Proofs.BatchProcessing.batchTimeLimit')
                   -> [String] -- ^ default extra options (prover specific)
                   -> Tactic_script
                   -> ATPTactic_script
parseTactic_script tLimit extOpts (Tactic_script ts) =
    maybe (ATPTactic_script { ts_timeLimit = tLimit,
                              ts_extraOpts = extOpts })
           id $ readMaybe ts
