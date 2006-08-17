{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
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

module SPASS.Prove (spassProver,spassProveGUI) where

import Logic.Prover

import SPASS.Sign
import SPASS.ProveHelp
import SPASS.Translate
import SPASS.ProverState

import qualified Common.AS_Annotation as AS_Anno

import ChildProcess
import ProcessClasses

import Text.Regex
import Data.List
import Data.Maybe
import qualified Control.Exception as Exception

import System

import HTk

import GUI.GenericATP
import GUI.GenericATPState

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
spassProver :: Prover Sign Sentence String
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SoftFOL",
           prove = spassProveGUI
         }

-- * Main GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence String -- ^ theory consisting of a
                                             --   SPASS.Sign.Sign and a list of
                                             --   Named SPASS.Sign.Sentence
              -> IO([Proof_status String]) -- ^ proof status for each goal
spassProveGUI thName th =
    genericATPgui atpFun True (prover_name spassProver) thName th ""

    where
      atpFun = ATPFunctions
        { initialProverState = spassProverState,
          atpTransSenName = transSenName,
          atpInsertSentence = insertSentenceGen,
          goalOutput = showDFGProblem thName,
          proverHelpText = spassHelpText,
          batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
          fileExtensions = FileExtensions{problemOutput = ".dfg",
                                          proverOutput = ".spass",
                                          theoryConfiguration = ".spcf"},
          runProver = runSpass,
          createProverOptions = createSpassOptions}


-- * SPASS Interfacing Code

{- |
  Reads and parses the output of SPASS.
-}
parseSpassOutput :: ChildProcess -- ^ the SPASS process
                 -> IO (Maybe String, [String], [String], Int)
                    -- ^ (result, used axioms, complete output, used time)
parseSpassOutput spass = parseProtected (parseStart True) (Nothing, [], [], 0)
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
              return (Nothing, [], ["SPASS returned error: "++(show retval)], 0)
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
                      [line, "", "SPASS has been terminated."], 0)
                ChildExited retval ->
                  return (Nothing, [], output ++
                      [line, "", "SPASS returned error: " ++ (show retval)], 0)

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
          usedAxs' = maybe usedAxs (words . head) usedAxsMatch
          tUsed' = maybe tUsed (calculateTime) $ matchRegex re_tu line
      if seq (length line) $ isJust (matchRegex re_stop line')
        then do
          _ <- waitForChildProcess spass
          return (res', usedAxs', output ++ [line'], tUsed')
        else
          parseProtected parseIt (res', usedAxs', output ++ [line'], tUsed')

    -- regular expressions used for parsing
    re_start = mkRegex ".*SPASS-START.*"
    re_stop = mkRegex ".*SPASS-STOP.*"
    re_sb = mkRegex "SPASS beiseite: (.*)$"
    re_ua = mkRegex "Formulae used in the proof.*:(.*)$"
    re_tu = mkRegex $ "SPASS spent\t([0-9]+):([0-9]+):([0-9]+)\\.([0-9]+) "
                      ++ "on the problem.$"
    calculateTime matches = if (not $ length matches == 4) then (0::Int)
       else
        (read hs)*10 + (read s)*1000 + (read m)*60000 + (read h)*3600000 :: Int
      where
        h  = matches !! 0
        m  = matches !! 1
        s  = matches !! 2
        hs = matches !! 3

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SPASSProverState -- ^ logical part containing the input Sign and
                             --  axioms and possibly goals that have been proved
                             --  earlier as additional axioms
         -> GenericConfig String -- ^ configuration to use
         -> Bool -- ^ True means save DFG file
         -> String -- ^ name of the theory in the DevGraph
         -> AS_Anno.Named SPTerm -- ^ goal to prove
         -> IO (ATPRetval, GenericConfig String)
             -- ^ (retval, configuration with proof status and complete output)
runSpass sps cfg saveDFG thName nGoal = do
  putStrLn ("running 'SPASS" ++ (concatMap (' ':) allOptions) ++ "'")
  spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
  Exception.catch (runSpassReal spass)
    (\ excep -> do
      -- kill spass process
      destroy spass
      _ <- waitForChildProcess spass
      return (case excep of
                -- this is supposed to distinguish "fd ... vanished"
                -- errors from other exceptions
                Exception.IOException e ->
                    (ATPError ("Internal error communicating "++
                               "with SPASS.\n"++show e),
                              emptyConfig (prover_name spassProver)
                                          (AS_Anno.senName nGoal) "")
                _ -> (ATPError ("Error running SPASS.\n"++show excep),
                        emptyConfig (prover_name spassProver)
                                    (AS_Anno.senName nGoal) "")
             ))

  where
    runSpassReal spass = do
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return
                 (ATPError "Could not start SPASS. Is SPASS in your $PATH?",
                  emptyConfig (prover_name spassProver)
                              (AS_Anno.senName nGoal) "")
        else do
          prob <- showDFGProblem thName sps nGoal (createSpassOptions cfg)
          when saveDFG
               (writeFile (thName++'_':AS_Anno.senName nGoal++".dfg") prob)
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
        (openProof_status (AS_Anno.senName nGoal) (prover_name spassProver) "")
        {tacticScript = Tactic_script
          {ts_timeLimit = configTimeLimit cfg,
           ts_extraOpts = unwords opts} }

    proof_stat res usedAxs options out
      | isJust res && elem (fromJust res) proved =
          (ATPSuccess,
           (defaultProof_status options)
           { goalStatus = Proved $ if elem (AS_Anno.senName nGoal) usedAxs
                                   then Nothing
                                   else Just False
           , usedAxioms = filter (/=(AS_Anno.senName nGoal)) usedAxs
           , proofTree = spassProof $ unlines out })
      | isJust res && elem (fromJust res) disproved =
          (ATPSuccess,
           (defaultProof_status options) { goalStatus = Disproved } )
      | isJust res && elem (fromJust res) timelimit =
          (ATPTLimitExceeded, defaultProof_status options)
      | isNothing res =
          (ATPError "Internal error.", defaultProof_status options)
      | otherwise = (ATPSuccess, defaultProof_status options)
    proved = ["Proof found."]
    disproved = ["Completion found."]
    timelimit = ["Ran out of time."]


{- |
  Creates a list of all options the SPASS prover runs with.
  That includes the defaults -DocProof and -Timelimit.
-}
createSpassOptions :: GenericConfig String -> [String]
createSpassOptions cfg = 
    (cleanOptions cfg) ++ ["-DocProof", "-TimeLimit="
                             ++ (show $ configTimeLimit cfg)]

{- |
  Filters extra options and just returns the non standard options.
-}    
cleanOptions :: GenericConfig String -> [String]
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
spassProof :: String -- ^ SPASS output containing proof tree
           -> String -- ^ extracted proof tree
spassProof pr =
    let getMatch = matchRegex re_proof_tree pr
        re_proof_tree = mkRegex $ "\nHere is a proof with depth.*:\n"
                               ++ "(.*)\nFormulae used in the proof"
    in maybe [] head getMatch
