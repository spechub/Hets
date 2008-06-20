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

import OWL.Sign
-- import OWL.PrintOWL
import OWL.PrintRDF
import OWL.AS

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import qualified Data.Map as Map

import Data.List (isPrefixOf)
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import qualified Control.Concurrent as Concurrent

import HTk
import System
import System.IO
import System.Process
import GUI.GenericATP
import GUI.GenericATPState
import Proofs.BatchProcessing
import Common.DefaultMorphism
import GUI.HTkUtils

-- import GUI.GenericATP (guiDefaultTimeLimit)
-- import GUI.GenericATPState
import GHC.Read (readEither)


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
                 -> PelletProverState
pelletProverState sig oSens = PelletProverState
         { ontologySign = sig
          ,initialState = filter AS_Anno.isAxiom oSens }

{- |
  The Prover implementation. First runs the batch prover (with graphical feedback), then starts the GUI prover.
-}
pelletProver :: Prover Sign Sentence () ATP_ProofTree
pelletProver = (mkProverTemplate "Pellet" () pelletGUI)
    { proveCMDLautomatic = Just pelletCMDLautomatic
    , proveCMDLautomaticBatch = Just pelletCMDLautomaticBatch }

pelletConsChecker :: ConsChecker Sign Sentence () (DefaultMorphism Sign) ATP_ProofTree
pelletConsChecker = mkProverTemplate "pellet" () consCheck


{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Sentence ATP_ProofTree PelletProverState
atpFun thName = ATPFunctions
    { initialProverState = pelletProverState,
      atpTransSenName = id,   -- transSenName,
      atpInsertSentence = insertOWLSentence,
      goalOutput = showOWLProblem thName,
      proverHelpText = "no help for pellet available",
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
           -> Theory Sign Sentence ATP_ProofTree
           -> IO([Proof_status ATP_ProofTree]) -- ^ proof status for each goal
pelletGUI thName th =
    genericATPgui (atpFun thName) True (prover_name pelletProver) thName th $
                  ATP_ProofTree ""

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status ATP_ProofTree]))
           -- ^ Proof status for goals and lemmas
pelletCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name pelletProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the Pellet prover via MathServe.
  Pellet specific functions are omitted by data type ATPFunctions.
-}
pelletCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ATP_ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ATP_ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
pelletCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name pelletProver) thName
        (parseTactic_script batchTimeLimit [] defTS) th (ATP_ProofTree "")

-- * Main prover functions
{- |
  Runs the Pellet service.
-}

spamOutput :: Proof_status ATP_ProofTree -> IO ()
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
             do createInfoWindow "Pellet consistency check"
                                     "This ontology is consistent."
                createTextSaveDisplay "Pellet prover" ("./"++ dName ++".pellet.log")
                 (
                 -- "I found a model for the theory " ++
                 -- dName ++". :) \n" ++
                 show dTree
                 )

        Proved (Just False) ->   -- not consistent
             do createInfoWindow "Pellet consistency check"
                                     "This ontology is not consistent."
                createTextSaveDisplay "Pellet prover" ("./"++ dName ++".pellet.log")
                 (
                 -- "I found a model for the theory " ++
                 -- dName ++". :) \n" ++
                 show dTree
                 )

        Proved Nothing -> return ()  -- todo: another errors


consCheck :: String
          -> TheoryMorphism Sign Sentence (DefaultMorphism Sign) ATP_ProofTree
          -> IO([Proof_status ATP_ProofTree])
consCheck thName tm =
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
                                       (toNamedList nSens)
          -- problem     = showOWLProblemA thName proverStateI []
          problemS     = showOWLProblemS thName proverStateI []
          simpleOptions = "-consistency on -s off "
          extraOptions  = "-timeout " ++ (show timeLimitI)
          saveFileName  = (reverse $ fst $ span (/='/') $ reverse thName)
          tmpFileName   = saveFileName

          runPelletRealM :: IO([Proof_status ATP_ProofTree])
          runPelletRealM = do
              hasProgramm <- system ("cd $PELLET_PATH; sh $PELLET_PATH/pellet.sh -version  > /dev/null 2> /dev/null")
              case hasProgramm of
                ExitFailure _ -> do
                   createInfoWindow "Pellet prover" "Pellet not found"
                   return [Proof_status
                           {
                            goalName = thName
                           , goalStatus = Open
                           , usedAxioms = getAxioms
                           , proverName = (prover_name pelletProver)
                           , proofTree  = ATP_ProofTree "Pellet not found"
                           , usedTime = timeToTimeOfDay $
                                        secondsToDiffTime 0
                           ,tacticScript  = tac
                           }]
                ExitSuccess -> do
                   when saveOWL
                          (writeFile (saveFileName ++".owl") problemS)
                   t <- getCurrentTime
                   let timeTmpFile = "/tmp/" ++ tmpFileName
                                     ++ (show $ utctDay t) ++
                                     "-" ++ (show $ utctDayTime t) ++ ".owl"
                       tmpURI = "file://"++timeTmpFile
                   writeFile timeTmpFile $ mkRealOWL problemS
                   let command = "cd $PELLET_PATH; sh pellet.sh "
                                 ++ simpleOptions ++ extraOptions
                                 ++ " -if " ++ tmpURI
                   putStrLn $ command
                   -- putStrLn $ mkRealOWL problemS
                   (_, outh, errh, proch) <- runInteractiveCommand command
                   (exCode, output, tUsed) <- parsePelletOut outh errh proch
                   let outState = proof_statM exCode simpleOptions
                                              output tUsed
                   spamOutput outState
                   return [outState]

          mkRealOWL probl =
              (show $ printRDF Map.empty sig)
                 ++ "\n\n" ++ probl ++ "\n</rdf:RDF>"

          proof_statM :: ExitCode -> String ->  [String]
                      -> Int -> Proof_status ATP_ProofTree
          proof_statM exitCode _ out tUsed =
              case exitCode of
                ExitSuccess ->   -- consistent
                    Proof_status
                    {
                     goalName = thName
                    , goalStatus = Proved (Just True)
                    , usedAxioms = getAxioms
                    , proverName = (prover_name pelletProver)
                    , proofTree = ATP_ProofTree (unlines out 
                                      ++ "\n\n" ++ mkRealOWL problemS)
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
                    , proofTree = ATP_ProofTree (unlines out 
                                      ++ "\n\n" ++ (mkRealOWL problemS))
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
                    , proofTree = ATP_ProofTree "can not run pellet."
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
                    , proofTree  = ATP_ProofTree (unlines out 
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
                    , proofTree =   ATP_ProofTree (unlines out
                                        ++ "\n\n" ++  (mkRealOWL problemS))
                    ,usedTime = timeToTimeOfDay $
                                secondsToDiffTime $ toInteger tUsed
                    ,tacticScript  = tac
                    }

          getAxioms =
               map AS_Anno.senAttr $ initialState proverStateI

        in
          runPelletRealM

-- TODO: Pellet Prove for single goals.
runPellet :: PelletProverState
           -- ^ logical part containing the input Sign and axioms and possibly
           --   goals that have been proved earlier as additional axioms
           -> GenericConfig ATP_ProofTree -- ^ configuration to use
           -> Bool -- ^ True means save TPTP file
           -> String -- ^ name of the theory in the DevGraph
           -> AS_Anno.Named Sentence -- ^ goal to prove
           -> IO (ATPRetval, GenericConfig ATP_ProofTree)
           -- ^ (retval, configuration with proof status and complete output)
runPellet sps cfg savePellet thName nGoal = do
  -- putStrLn ("running Pellet...")
  runPelletReal

  where
    simpleOptions = extraOpts cfg
    extraOptions  = maybe "-s off -cs"
        ( \ tl -> "-pc false" ++ " -to " ++ show tl ++ " -cs ")
        $ timeLimit cfg
    saveFileName  = thName++'_':AS_Anno.senAttr nGoal
    tmpFileName   = (reverse $ fst $ span (/='/') $ reverse thName) ++
                       '_':AS_Anno.senAttr nGoal
    -- tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg

    runPelletReal = do
      hasProgramm <- system ("sh $PELLET_PATH/pellet.sh -version  > /dev/null 2> /dev/null")
      case hasProgramm of
        ExitFailure _ -> return
            (ATPError "Could not start Pellet. Is Pellet in your $PATH?",
                  emptyConfig (prover_name pelletProver)
                              (AS_Anno.senAttr nGoal) $ ATP_ProofTree "")
        ExitSuccess -> do
          prob <- mkOWLGoalProblem
          when savePellet
            (writeFile (saveFileName ++".owl") prob)
          t <- getCurrentTime
          let timeTmpFile = "/tmp/" ++ tmpFileName ++ (show $ utctDay t) ++
                               "-" ++ (show $ utctDayTime t) ++ ".owl"
          writeFile timeTmpFile prob
          let command = "pellet " ++ extraOptions ++ " " ++ timeTmpFile
          -- putStrLn command
          (_, outh, errh, proch) <- runInteractiveCommand command
          (exCode, output, tUsed) <- parsePelletOut outh errh proch
          let (err, retval) = proof_stat exCode simpleOptions output tUsed
          return (err,
                  cfg{proof_status = retval,
                      resultOutput = output,
                      timeUsed     = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger tUsed})

    proof_stat exitCode options out tUsed =
            case exitCode of
              ExitSuccess -> (ATPSuccess, proved_status options tUsed)
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
                                    ATP_ProofTree "")
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
              ,proofTree =   ATP_ProofTree ""
              ,usedTime = timeToTimeOfDay $
                                 secondsToDiffTime $ toInteger ut
              ,tacticScript  = Tactic_script $ show $ ATPTactic_script
                               {ts_timeLimit = configTimeLimit cfg,
                                ts_extraOpts = opts}
                    }

    getAxioms = []

    mkOWLGoalProblem = do
        p <- showOWLProblem thName sps nGoal 
               (simpleOptions ++ ["Requested prover: Pellet"])
        return ((show $ printRDF Map.empty $ ontologySign sps)
                  ++ "\n\n" ++ p ++ "\n</rdf:RDF>")

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
                           else readLineAndParse
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
    in show (printRDF (mkAssMap (map AS_Anno.sentence namedSens)
                                Map.empty)
                      namedSens
            )

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
configTimeLimit :: GenericConfig ATP_ProofTree
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
    either (\_ -> ATPTactic_script { ts_timeLimit = tLimit,
                                     ts_extraOpts = extOpts })
           id
           (readEither ts :: Either String ATPTactic_script)


mkAssMap :: [Sentence]
         -> Map.Map IndividualURI OwlClassURI
         -> Map.Map IndividualURI OwlClassURI
mkAssMap [] m = m
mkAssMap (h:r) m =
    case h of
      OWLFact (ClassAssertion _ indUri (OWLClass cUri)) ->
          mkAssMap r (Map.insert indUri cUri m)
      _ -> mkAssMap r m
