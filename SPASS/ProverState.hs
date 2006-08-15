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

module SPASS.ProverState where

import SPASS.Sign
import SPASS.Conversions
import SPASS.Translate
import SPASS.PrintTPTP
import SPASS.Print ()

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.Utils (splitOn)
import Common.DocUtils

import Data.Maybe

import GUI.GenericATP (guiDefaultTimeLimit)
import GUI.GenericATPState

-- * Data structures

data SPASSProverState = SPASSProverState
    { initialLogicalPart :: SPLogicalPart}

-- * SPASS specific functions for prover GUI

{- |
  Creates an initial SPASS prover state with logical part.
-}
spassProverState :: Sign -- ^ SPASS signature
                 -> [AS_Anno.Named SPTerm] -- ^ list of named SPASS terms 
                                           --   containing axioms
                 -> SPASSProverState
spassProverState sign oSens' = SPASSProverState{
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axiomList)}
  where nSens = prepareSenNames transSenName oSens'
        axiomList = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SPASS term into SPASS prover state.
-}
insertSentenceGen :: SPASSProverState -- ^ prover state containing
                                      --   initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to add
                  -> SPASSProverState
insertSentenceGen pst s = pst{initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SPASS goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to print
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst nGoal opts = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  -- add SPASS command line settings and extra options
  let prob' = prob { settings = (settings prob) ++ (parseSPASSCommands opts) }
  return $ showDoc prob' ""

{- |
  Pretty printing SPASS goal in TPTP format.
-}
showTPTPProblem :: String -- ^ theory name
                -> SPASSProverState -- ^ prover state containing
                                    --   initial logical part
                -> AS_Anno.Named SPTerm -- ^ goal to print
                -> [String] -- ^ extra options
                -> IO String -- ^ formatted output of the goal
showTPTPProblem thName pst nGoal opts = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  -- add extra options as SPSettings with only one field filled
  let prob' = prob { settings = (settings prob) ++
                                (map (\opt -> SPFlag "" opt) opts) }
  return $ show $ printTPTP prob'

{- |
  Translates SPASS command line into [SPSetting].
-}
parseSPASSCommands :: [String] -- ^ SPASS command line options
                   -> [SPSetting] -- ^ parsed parameters and options
parseSPASSCommands comLine =
    map (\opt -> let splitOpt = splitOn '=' opt
                 in case length splitOpt of
                      0 -> SPFlag "" ""
                      1 -> SPFlag (head splitOpt) "1"
                      -- if multiple '=', texts are concatenated
                      _ -> SPFlag (head splitOpt) $ concat $ tail splitOpt
        ) $
        map undash comLine
    where
      -- remove '-' (multiple) at beginning of an option
      undash = dropWhile (\ch -> ch == '-')

{- |
  Returns the time limit from GenericConfig if available. Otherwise
  guiDefaultTimeLimit is returned.
-}
configTimeLimit :: GenericConfig String
                -> Int
configTimeLimit cfg = 
    maybe (guiDefaultTimeLimit) id $ timeLimit cfg
