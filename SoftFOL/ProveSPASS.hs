{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Rainer Grabbe,
                   Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{-
      - check if the theorem is used in the proof;
        if not, the theory is inconsistent;
        mark goal as proved and emmit a warning...

      - Implement a consistency checker based on GUI
-}

module SoftFOL.ProveSPASS (spassProver,
                           spassProveGUI,
                           spassProveCMDLautomatic,
                           spassProveCMDLautomaticBatch) where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Translate
import SoftFOL.ProverState

import ChildProcess as CP
import ProcessClasses
import HTk

import GUI.GenericATP
import GUI.GenericATPState
import Proofs.BatchProcessing

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import Common.ProofTree
import Common.Utils (splitOn)

import qualified Control.Concurrent as Concurrent
import qualified Control.Exception as Exception
import System.Exit
import Text.Regex
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay(..),midnight -- only in ghc-6.6.1: ,parseTime
                 )
-- * Prover implementation

{- |
  The Prover implementation.

  Implemented are: a prover GUI, and both commandline prover interfaces.
-}
spassProver :: Prover Sign Sentence SoftFOLMorphism () ProofTree
spassProver = (mkProverTemplate "SPASS" () spassProveGUI)
    { proveCMDLautomatic = Just spassProveCMDLautomatic
    , proveCMDLautomaticBatch = Just spassProveCMDLautomaticBatch }

-- * Main prover functions

-- ** Utility functions

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String -- ^ theory name
       -> ATPFunctions Sign Sentence ProofTree SoftFOLProverState
atpFun thName = ATPFunctions
    { initialProverState = spassProverState,
      atpTransSenName = transSenName,
      atpInsertSentence = insertSentenceGen,
      goalOutput = showDFGProblem thName,
      proverHelpText = "http://www.spass-prover.org/\n",
      batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
      fileExtensions = FileExtensions{problemOutput = ".dfg",
                                      proverOutput = ".spass",
                                      theoryConfiguration = ".spcf"},
      runProver = runSpass,
      createProverOptions = createSpassOptions }

{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible. Otherwise a default
  SPASS tactic script is returned.
-}
parseSpassTactic_script :: Tactic_script
                        -> ATPTactic_script
parseSpassTactic_script =
    parseTactic_script batchTimeLimit ["-Stdin", "-DocProof"]

-- ** GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
spassProveGUI :: String -- ^ theory name
          -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
             --   'SPASS.Sign.Sign' and a list of Named 'SPASS.Sign.Sentence'
          -> IO([Proof_status ProofTree]) -- ^ proof status for each goal
spassProveGUI thName th =
    genericATPgui (atpFun thName) True (prover_name spassProver) thName th
                  emptyProofTree

-- ** command line functions

{- |
  Implementation of 'Logic.Prover.proveCMDLautomatic' which provides an
  automatic command line interface for a single goal.
  SPASS specific functions are omitted by data type ATPFunctions.
-}
spassProveCMDLautomatic ::
           String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
                                -- signature and a list of Named sentence
        -> IO (Result.Result ([Proof_status ProofTree]))
           -- ^ Proof status for goals and lemmas
spassProveCMDLautomatic thName defTS th =
    genericCMDLautomatic (atpFun thName) (prover_name spassProver) thName
        (parseSpassTactic_script defTS) th emptyProofTree

{- |
  Implementation of 'Logic.Prover.proveCMDLautomaticBatch' which provides an
  automatic command line interface to the SPASS prover.
  SPASS specific functions are omitted by data type ATPFunctions.
-}
spassProveCMDLautomaticBatch ::
           Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Concurrent.MVar (Result.Result [Proof_status ProofTree])
           -- ^ used to store the result of the batch run
        -> String -- ^ theory name
        -> Tactic_script -- ^ default tactic script
        -> Theory Sign Sentence ProofTree -- ^ theory consisting of a
           --   'SoftFOL.Sign.Sign' and a list of Named 'SoftFOL.Sign.Sentence'
        -> IO (Concurrent.ThreadId,Concurrent.MVar ())
           -- ^ fst: identifier of the batch thread for killing it
           --   snd: MVar to wait for the end of the thread
spassProveCMDLautomaticBatch inclProvedThs saveProblem_batch resultMVar
                        thName defTS th =
    genericCMDLautomaticBatch (atpFun thName) inclProvedThs saveProblem_batch
        resultMVar (prover_name spassProver) thName
        (parseSpassTactic_script defTS) th emptyProofTree


-- * SPASS Interfacing Code

{- |
  Reads and parses the output of SPASS.
-}
parseSpassOutput :: ChildProcess -- ^ the SPASS process
                 -> IO (Maybe String, [String], [String], TimeOfDay)
                    -- ^ (result, used axioms, complete output, used time)
parseSpassOutput spass = parseProtected (parseStart True)
                                        (Nothing, [], [], midnight)
  where

    -- check for errors. unfortunately we cannot just read from SPASS until an
    -- EOF since readMsg will just wait forever on EOF.
    parseProtected f (res, usedAxs, output, tUsed) = do
      e <- getToolStatus spass
      case e of
        Nothing
          -- still running
          -> f (res, usedAxs, output, tUsed)
        Just (ExitFailure retval)
          -- returned error
          -> do
              _ <- waitForChildProcess spass
              return (Nothing, [],
                      ["SPASS returned error: "++(show retval)]
                     , tUsed)
        Just ExitSuccess
          -- completed successfully. read remaining output.
          -> f (res, usedAxs, output, tUsed)

    -- the first line of SPASS output is always empty.
    -- the second contains SPASS-START in the usual case
    -- and an error message in case of an error
    parseStart firstline (res, usedAxs, output, tUsed) = do
      line <- readMsg spass
      if firstline
        -- ignore empty first line
        then parseProtected (parseStart False)
                            (res, usedAxs, output ++ [""], tUsed)
        -- check for a potential error
        else do
          let startMatch = matchRegex re_start line
          if isJust startMatch
            -- got SPASS-START. continue parsing
            then parseProtected parseIt (res, usedAxs, output ++ [line], tUsed)
            -- error. abort parsing
            else do
              e <- waitForChildProcess spass
              case e of
                ChildTerminated ->
                  return (Nothing, [], output ++
                          [line, "", "SPASS has been terminated."]
                         , tUsed)
                ChildExited retval ->
                  return (Nothing, [], output ++
                          [line, "", "SPASS returned error: " ++ (show retval)]
                         , tUsed)

    -- actual parsing. tries to read from SPASS until ".*SPASS-STOP.*" matches.
    parseIt (res, usedAxs, output, tUsed) = do
      line <- readMsg spass
      -- replace tabulators with each 8 spaces
      let line' = foldr (\ch li -> if ch == '\x9'
                                   then "        "++li
                                   else ch:li) "" line
          resMatch = matchRegex re_sb line'
          res' = maybe res (Just . head) resMatch
          usedAxsMatch = matchRegex re_ua line'
          usedAxs' = maybe usedAxs (\ uas -> words (uas !! 1)) usedAxsMatch
          tUsed' = maybe tUsed calculateTime $ matchRegex re_tu line
      if seq (length line) $ isJust (matchRegex re_stop line')
        then do
          _ <- waitForChildProcess spass
          return (res', usedAxs', output ++ [line'], tUsed')
        else
          parseProtected parseIt (res', usedAxs', output ++ [line'], tUsed')

    -- regular expressions used for parsing
    re_start = mkRegex "(.*)SPASS-START(.*)"
    re_stop = mkRegex "(.*)SPASS-STOP(.*)"
    re_sb = mkRegex "SPASS beiseite: (.*)$"
    re_ua = mkRegex "Formulae used in the proof(.*):(.*)$"
    re_tu = mkRegex $ "SPASS spent\t([0-9:.]+) "
                      ++ "on the problem.$"
    calculateTime str =
        if null str then midnight
        else
    -- the following line is only nice with ghc-6.6.1
    --    (maybe midnight id . parseTime defaultTimeLocale "%k:%M:%S%Q")
            parseTimeOfDay $ head str

parseTimeOfDay :: String -> TimeOfDay
parseTimeOfDay str =
    case splitOn ':' str of
      [h,m,s] -> TimeOfDay { todHour = read h
                           , todMin  = read m
                           , todSec  = realToFrac ((read s)::Double)
                           }
      _ -> error "SoftFOL.Prove: wrong time format"

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SoftFOLProverState -- ^ logical part containing the input Sign and
                     --  axioms and possibly goals that have been proved
                     --  earlier as additional axioms
         -> GenericConfig ProofTree -- ^ configuration to use
         -> Bool -- ^ True means save DFG file
         -> String -- ^ name of the theory in the DevGraph
         -> AS_Anno.Named SPTerm -- ^ goal to prove
         -> IO (ATPRetval, GenericConfig ProofTree)
             -- ^ (retval, configuration with proof status and complete output)
runSpass sps cfg saveDFG thName nGoal = do
--  putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions) ++ "'")
  spass <- newChildProcess "SPASS" [CP.arguments allOptions]
  Exception.catch (runSpassReal spass)
    (\ excep -> do
      -- kill spass process
      destroy spass
      _ <- waitForChildProcess spass
      excepToATPResult (prover_name spassProver) nGoal excep)

  where
    runSpassReal spass = do
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return
                 (ATPError "Could not start SPASS. Is SPASS in your $PATH?",
                  emptyConfig (prover_name spassProver)
                              (AS_Anno.senAttr nGoal) emptyProofTree)
        else do
          prob <- showDFGProblem thName sps nGoal (createSpassOptions cfg)
          when saveDFG
               (writeFile (thName++'_':AS_Anno.senAttr nGoal++".dfg") prob)
          sendMsg spass prob
          (res, usedAxs, output, tUsed) <- parseSpassOutput spass
          let (err, retval) = proof_stat res usedAxs extraOptions output
          return (err,
                  cfg{proof_status = retval,
                      resultOutput = output,
                      timeUsed     = tUsed})

    allOptions = ("-Stdin"):(createSpassOptions cfg)
    extraOptions = ("-DocProof"):(cleanOptions cfg)
    defaultProof_status opts =
        (openProof_status (AS_Anno.senAttr nGoal) (prover_name spassProver) $
                           emptyProofTree)
        {tacticScript = Tactic_script $ show $ ATPTactic_script
          {ts_timeLimit = configTimeLimit cfg,
           ts_extraOpts = opts} }

    proof_stat res usedAxs options out
      | isJust res && elem (fromJust res) proved =
          (ATPSuccess,
           (defaultProof_status options)
           { goalStatus = Proved $ if elem (AS_Anno.senAttr nGoal) usedAxs
                                   then Nothing
                                   else Just False
           , usedAxioms = filter (/=(AS_Anno.senAttr nGoal)) usedAxs
           , proofTree = ProofTree $ spassProof out })
      | isJust res && elem (fromJust res) disproved =
          (ATPSuccess,
           (defaultProof_status options) { goalStatus = Disproved } )
      | isJust res && elem (fromJust res) timelimit =
          (ATPTLimitExceeded, defaultProof_status options)
      | isNothing res =
          (ATPError (unlines ("Internal error.":out)),
                    defaultProof_status options)
      | otherwise = (ATPSuccess, defaultProof_status options)
    proved = ["Proof found."]
    disproved = ["Completion found."]
    timelimit = ["Ran out of time."]


{- |
  Creates a list of all options the SPASS prover runs with.
  That includes the defaults -DocProof and -Timelimit.
-}
createSpassOptions :: GenericConfig ProofTree -> [String]
createSpassOptions cfg =
    (cleanOptions cfg) ++ ["-DocProof", "-TimeLimit="
                             ++ (show $ configTimeLimit cfg)]

{- |
  Filters extra options and just returns the non standard options.
-}
cleanOptions :: GenericConfig ProofTree -> [String]
cleanOptions cfg =
    filter (\ opt -> not (or (map (flip isPrefixOf opt)
                                  filterOptions)))
           (extraOpts cfg)
    where
      filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]

{- |
  Extract proof tree from SPASS output. This will be the String between
  "Here is a proof" and "Formulae used in the proof"
-}
spassProof :: [String] -- ^ SPASS output containing proof tree
           -> String -- ^ extracted proof tree
spassProof =
        unlines . fst . break (isPrefixOf "Formulae used in the proof")
             . (\ l -> if null l then l else tail l)
             . snd . break (isPrefixOf "Here is a proof with depth")
