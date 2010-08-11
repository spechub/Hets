{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
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

-- * Data structures

data SoftFOLProverState = SoftFOLProverState
    { initialLogicalPart :: SPLogicalPart}

-- * SoftFOL specific functions for prover GUI

{- |
  Creates an initial SoftFOL prover state with logical part.
-}
spassProverState
    :: Sign -- ^ SoftFOL signature
    -> [AS_Anno.Named SPTerm]
       -- ^ list of named SoftFOL terms containing axioms
    -> [FreeDefMorphism SPTerm SoftFOLMorphism]  -- ^ freeness constraints
    -> SoftFOLProverState
spassProverState sign oSens' _ = SoftFOLProverState {
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axiomList)}
  where nSens = prepareSenNames transSenName oSens'
        axiomList = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SoftFOL term into SoftFOL prover state.
-}
insertSentenceGen
    :: SoftFOLProverState
       -- ^ prover state containing initial logical part
    -> AS_Anno.Named SPTerm -- ^ goal to add
    -> SoftFOLProverState
insertSentenceGen pst s = pst {initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SoftFOL goal in DFG format.
-}
showDFGProblem
    :: String -- ^ theory name
    -> SoftFOLProverState
       -- ^ prover state containing initial logical part
    -> AS_Anno.Named SPTerm -- ^ goal to print
    -> [String] -- ^ extra options
    -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst nGoal opts = do
  prob <- genSoftFOLProblem thName (initialLogicalPart pst) $ Just nGoal
  -- add SPASS command line settings and extra options
  let prob' = prob { settings = settings prob ++ parseSPASSCommands opts }
  return $ showDoc prob' ""

{- |
  Pretty printing SoftFOL-model-finding-problem in TPTP format.
-}
showTPTPProblemM
    :: String -- ^ theory name
    -> SoftFOLProverState -- ^ prover state containing initial logical part
    -> [String] -- ^ extra options
    -> IO String -- ^ formatted output of the goal
showTPTPProblemM thName pst = showTPTPProblemAux thName pst Nothing

{- |
  Pretty printing SoftFOL goal in TPTP format.
-}
showTPTPProblem
    :: String -- ^ theory name
    -> SoftFOLProverState -- ^ prover state containing initial logical part
    -> AS_Anno.Named SPTerm -- ^ goal to print
    -> [String] -- ^ extra options
    -> IO String -- ^ formatted output of the goal
showTPTPProblem thName pst = showTPTPProblemAux thName pst . Just

showTPTPProblemAux
    :: String -- ^ theory name
    -> SoftFOLProverState -- ^ prover state containing initial logical part
    -> Maybe (AS_Anno.Named SPTerm) -- ^ possible goal to print
    -> [String] -- ^ extra options
    -> IO String -- ^ formatted output of the goal
showTPTPProblemAux thName pst mGoal opts = do
  prob <- genSoftFOLProblem thName (initialLogicalPart pst) mGoal
  -- add extra options as SPSettings with only one field filled
  let prob' = prob { settings = settings prob
                                ++ [SPSettings SPASS
                                     $ map (\ opt ->
                                           SPFlag "set_flag" [opt]) opts] }
  return $ show $ printTPTP prob'

{- |
  Translates SPASS command line into [SPSetting].
-}
parseSPASSCommands :: [String] -- ^ SPASS command line options
                   -> [SPSetting] -- ^ parsed parameters and options
parseSPASSCommands comLine =
    [SPSettings SPASS $
            map (\ opt -> case splitOn '=' $ dropWhile (== '-') opt of
                 [] -> error "parseSPASSCommands"
                 [h] -> SPFlag "set_flag" [h, "1"]
                   -- if multiple '=', texts are concatenated
                 h : r -> SPFlag "set_flag" [h, concat r]
                ) comLine ]
