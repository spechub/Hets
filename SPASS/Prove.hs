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
import SPASS.Conversions
import SPASS.ProveHelp
import SPASS.Translate
import SPASS.Print (genSPASSProblem)

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.PrettyPrint

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
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProveGUI
         }

-- ** Data structures

data SPASSProverState = SPASSProverState
    { initialLogicalPart :: SPLogicalPart}


-- ** SPASS specific functions for prover GUI

{- |
  Creates an initial SPASS prover state with logical part.
-}
spassProverState :: Sign -- ^ SPASS signature
                 -> [AS_Anno.Named SPTerm] -- ^ list of named SPASS terms containing axioms
                 -> SPASSProverState
spassProverState sign oSens' = SPASSProverState{
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axioms)}
  where nSens = prepareSenNames transSenName oSens'
        axioms = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SPASS term into SPASS prover state.
-}
insertSentenceGen :: SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to add
                  -> SPASSProverState
insertSentenceGen pst s = pst{initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SPASS goal in DFG format.
-}
showPrettyProblem :: String -- ^ theory name
                  -> SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to print
                  -> IO String -- ^ formatted output of the goal
showPrettyProblem thName pst nGoal = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  return $ showPretty prob ""


-- * Main GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
spassProveGUI :: String -- ^ theory name
              -> Theory Sign Sentence () -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
              -> IO([Proof_status ()]) -- ^ proof status for each goal
spassProveGUI thName th =
    genericATPgui atpFun True (prover_name spassProver) thName th ()

    where
      atpFun = ATPFunctions
        { initialProverState = spassProverState,
          atpTransSenName = transSenName,
          atpInsertSentence = insertSentenceGen,
          goalOutput = showPrettyProblem thName,
          proverHelpText = spassHelpText,
          batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
          fileExtensions = FileExtensions{problemOutput = ".dfg",
                                          proverOutput = ".spass",
                                          theoryConfiguration = ".spcf"},
          runProver = runSpass}


-- * SPASS Interfacing Code

{- |
  Reads and parses the output of SPASS.
-}
parseSpassOutput :: ChildProcess -- ^ the SPASS process
                 -> IO (Maybe String, [String], [String]) -- ^ (result, used axioms, complete output)
parseSpassOutput spass = parseProtected (parseStart True) (Nothing, [], [])
  where

    -- check for errors. unfortunately we cannot just read from SPASS until an
    -- EOF since readMsg will just wait forever on EOF.
    parseProtected f (res, usedAxs, output) = do
      e <- getToolStatus spass
      case e of
        Nothing
          -- still running
          -> f (res, usedAxs, output)
        Just (ExitFailure retval)
          -- returned error
          -> do
              _ <- waitForChildProcess spass
              return (Nothing, [], ["SPASS returned error: "++(show retval)])
        Just ExitSuccess
          -- completed successfully. read remaining output.
          -> f (res, usedAxs, output)

    -- the first line of SPASS output is always empty.
    -- the second contains SPASS-START in the usual case
    -- and an error message in case of an error
    parseStart firstline (res, usedAxs, output) = do
      line <- readMsg spass
      if firstline
        -- ignore empty first line
        then parseProtected (parseStart False) (res, usedAxs, output ++ [""])
        -- check for a potential error
        else do
          let startMatch = matchRegex re_start line
          if isJust startMatch
            -- got SPASS-START. continue parsing
            then parseProtected parseIt (res, usedAxs, output ++ [line])
            -- error. abort parsing
            else do
              e <- waitForChildProcess spass
              case e of
                ChildTerminated ->
                  return (Nothing, [], output ++ [line, "", "SPASS has been terminated."])
                ChildExited retval ->
                  return (Nothing, [], output ++ [line, "", "SPASS returned error: "++(show retval)])

    -- actual parsing. tries to read from SPASS until ".*SPASS-STOP.*" matches.
    parseIt (res, usedAxs, output) = do
      line <- readMsg spass
      -- replace tabulators with each 8 spaces
      let line' = foldr (\ch li -> if ch == '\x9'
                                   then "        "++li
                                   else ch:li) "" line
      let resMatch = matchRegex re_sb line'
      let res' = if isJust resMatch then (Just $ head $ fromJust resMatch) else res
      let usedAxsMatch = matchRegex re_ua line'
      let usedAxs' = if isJust usedAxsMatch then (words $ head $ fromJust usedAxsMatch) else usedAxs
      if seq (length line) $ isJust (matchRegex re_stop line')
        then do
          _ <- waitForChildProcess spass
          return (res', usedAxs', output ++ [line'])
        else
          parseProtected parseIt (res', usedAxs', output ++ [line'])

    -- regular expressions used for parsing
    re_start = mkRegex ".*SPASS-START.*"
    re_stop = mkRegex ".*SPASS-STOP.*"
    re_sb = mkRegex "SPASS beiseite: (.*)$"
    re_ua = mkRegex "Formulae used in the proof.*:(.*)$"


{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: SPASSProverState -- ^ logical part containing the input Sign and axioms and possibly goals that have been proved earlier as additional axioms
         -> GenericConfig () -- ^ configuration to use
         -> Bool -- ^ True means save DFG file
         -> String -- ^ name of the theory in the DevGraph
         -> AS_Anno.Named SPTerm -- ^ goal to prove
         -> IO (ATPRetval, GenericConfig ()) -- ^ (retval, configuration with proof status and complete output)
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
                                          (AS_Anno.senName nGoal) ())
                _ -> (ATPError ("Error running SPASS.\n"++show excep),
                        emptyConfig (prover_name spassProver)
                                    (AS_Anno.senName nGoal) ())
             ))

  where
    runSpassReal spass = do
      -- check if SPASS is running
      e <- getToolStatus spass
      if isJust e
        then return
                 (ATPError "Could not start SPASS. Is SPASS in your $PATH?",
                  emptyConfig (prover_name spassProver)
                              (AS_Anno.senName nGoal) ())
        else do
          let lp = initialLogicalPart sps
          prob <- genSPASSProblem thName lp (Just nGoal)
          when saveDFG
               (writeFile (thName++'_':AS_Anno.senName nGoal++".dfg")
                          (showPretty prob ""))
          sendMsg spass (showPretty prob "")
          (res, usedAxs, output) <- parseSpassOutput spass
          let (err, retval) = proof_stat res usedAxs cleanOptions
          return (err,
                  cfg{proof_status = retval,
                      resultOutput = output})

    filterOptions = ["-DocProof", "-Stdin", "-TimeLimit"]
    cleanOptions = filter (\ opt -> not (or (map (flip isPrefixOf opt)
                                                 filterOptions)))
                          (extraOpts cfg)
    tLimit = if isJust (timeLimit cfg)
               then fromJust (timeLimit cfg)
               -- this is OK. the batch prover always has the time limit set
               else guiDefaultTimeLimit
    allOptions = cleanOptions ++ ["-DocProof", "-Stdin", "-TimeLimit=" ++ (show tLimit)]
    defaultProof_status opts =
        (openProof_status (AS_Anno.senName nGoal) (prover_name spassProver) ())
        {tacticScript = Tactic_script $ concatMap (' ':) opts}

    proof_stat res usedAxs options
      | isJust res && elem (fromJust res) proved =
          (ATPSuccess,
           (defaultProof_status options)
           { goalStatus = Proved $ if elem (AS_Anno.senName nGoal) usedAxs
                                   then Nothing
                                   else Just False
           , usedAxioms = filter (/=(AS_Anno.senName nGoal)) usedAxs })
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
