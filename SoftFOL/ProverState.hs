{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Data structures and initialising functions for Prover state and configurations.

-}

module SoftFOL.ProverState where

import Logic.Prover

import SoftFOL.Sign
import SoftFOL.Conversions
import SoftFOL.Translate
import SoftFOL.PrintTPTP
import SoftFOL.Print ()

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.Utils (splitOn)
import Common.DocUtils
import qualified Control.Exception as Exception

import Data.Maybe
import GHC.Read (readEither)

import GUI.GenericATP (guiDefaultTimeLimit)
import GUI.GenericATPState

-- * Data structures

data SoftFOLProverState = SoftFOLProverState
    { initialLogicalPart :: SPLogicalPart}

-- * SoftFOL specific functions for prover GUI

{- |
  Creates an initial SoftFOL prover state with logical part.
-}
spassProverState :: Sign -- ^ SoftFOL signature
                 -> [AS_Anno.Named SPTerm] -- ^ list of named SoftFOL terms 
                                           --   containing axioms
                 -> SoftFOLProverState
spassProverState sign oSens' = SoftFOLProverState{
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axiomList)}
  where nSens = prepareSenNames transSenName oSens'
        axiomList = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SoftFOL term into SoftFOL prover state.
-}
insertSentenceGen :: SoftFOLProverState -- ^ prover state containing
                                      --   initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to add
                  -> SoftFOLProverState
insertSentenceGen pst s = pst{initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SoftFOL goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> SoftFOLProverState -- ^ prover state containing
                                      -- initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to print
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst nGoal opts = do
  prob <- genSoftFOLProblem thName (initialLogicalPart pst) $ Just nGoal
  -- add SPASS command line settings and extra options
  let prob' = prob { settings = (settings prob) ++ (parseSPASSCommands opts) }
  return $ showDoc prob' ""

{- |
  Pretty printing SoftFOL goal in TPTP format.
-}
showTPTPProblem :: String -- ^ theory name
                -> SoftFOLProverState -- ^ prover state containing
                                    --   initial logical part
                -> AS_Anno.Named SPTerm -- ^ goal to print
                -> [String] -- ^ extra options
                -> IO String -- ^ formatted output of the goal
showTPTPProblem thName pst nGoal opts = do
  prob <- genSoftFOLProblem thName (initialLogicalPart pst) $ Just nGoal
  -- add extra options as SPSettings with only one field filled
  let prob' = prob { settings = (settings prob) 
                                ++ [SPSettings SPASS
                                     (map (\opt ->  
                                           (SPFlag "set_flag" [opt])) opts)] }
                                 -- (SPSetting is changed, see Sign.hs)
  return $ show $ printTPTP prob'

{- |
  Translates SPASS command line into [SPSetting].
-}
parseSPASSCommands :: [String] -- ^ SPASS command line options
                   -> [SPSetting] -- ^ parsed parameters and options
parseSPASSCommands comLine =
    let body =
            map (\opt -> let splitOpt = splitOn '=' opt
                         in case length splitOpt of
                              0 -> SPFlag "set_flag" [(head splitOpt), "0"]
                              1 -> SPFlag "set_flag" [(head splitOpt), "1"]
                         -- if multiple '=', texts are concatenated
                              _ -> SPFlag "set_flag" [(head splitOpt), concat $ tail splitOpt]
                ) $ map undash comLine
    in [SPSettings SPASS body]   -- (SPSetting is changed, see Sign.hs)

    where
      -- remove '-' (multiple) at beginning of an option
      undash = dropWhile (\ch -> ch == '-')

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

-- | Converts a thrown exception into an ATP result (ATPRetval and proof tree).
excepToATPResult :: String -- ^ name of running prover
                 -> AS_Anno.Named SPTerm -- ^ goal to prove
                 -> Exception.Exception -- ^ occured exception
                 -> IO (ATPRetval, GenericConfig ATP_ProofTree) -- ^ (retval,
                    -- configuration with proof status and complete output)
excepToATPResult prName nGoal excep = return $ case excep of
    -- this is supposed to distinguish "fd ... vanished"
    -- errors from other exceptions
    Exception.IOException e ->
        (ATPError ("Internal error communicating with " ++ prName ++ ".\n"
                   ++ show e), emptyCfg)
    Exception.AsyncException Exception.ThreadKilled ->
        (ATPBatchStopped, emptyCfg)
    _ -> (ATPError ("Error running " ++ prName ++ ".\n" ++ show excep),
          emptyCfg)
  where
    emptyCfg = emptyConfig prName (AS_Anno.senName nGoal) $ ATP_ProofTree ""
