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

import Logic.Prover

import SPASS.Sign
import SPASS.Conversions
import SPASS.Translate
import SPASS.PrintTPTP
import SPASS.Print ()
import SPASS.MathServParsing

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
  Maps a MathServResponse record into a GenericConfig with Proof_status.
  If there is no FoAtpResult available, an ATPError and a corresponding
  MWFailure message (hopefully filled) will be returned .
-}
mapMathServResponse :: MathServResponse -- ^ Parsed MathServ data
                    -> GenericConfig () -- ^ configuration to use
                    -> AS_Anno.Named SPTerm -- ^ goal to prove
                    -> String -- ^ prover name
                    -> (ATPRetval, GenericConfig ())
                    -- ^ (retval, configuration with proof status and
                    --    complete output)
mapMathServResponse msr cfg nGoal prName =
    maybe (ATPError "Internal Error.",
           cfg { proof_status = defaultProof_status nGoal
                    (prName ++ " [via MathServ]") (configTimeLimit cfg),
                 resultOutput = maybe [] lines (failure msr) })
          (\res -> mapProverResult res cfg nGoal prName)
          (foAtpResult msr)

{- |
  Maps a FoAtpResult record into a GenericConfig with Proof_status.
  !! Comment missing !!
-}
mapProverResult :: MWFoAtpResult -- ^ Parsed FoATPResult data
                -> GenericConfig () -- ^ configuration to use
                -> AS_Anno.Named SPTerm -- ^ goal to prove
                -> String -- ^ prover name
                -> (ATPRetval, GenericConfig ())
                -- ^ (retval, configuration with proof status, complete output)
mapProverResult atpResult cfg nGoal prName =
    let res = mapToGoalStatus $ systemStatus atpResult
        output = lines $ unTab $ outputStr atpResult
        timeout = (foStatus $ systemStatus atpResult) == Timeout
        
        -- get real prover name if Broker was used
        brokerName = "MSBroker"
        prName' = if (prName == brokerName)
                     then (usedProverName $ systemStr atpResult)
                          ++ " [via MathServBroker]"
                     else prName ++ " [via MathServ]"
        
        usedAxs = if (null $ axioms $ proof atpResult)
                    then [AS_Anno.senName nGoal]
                    else words $ axioms $ proof atpResult
        (atpErr, retval) = proof_stat nGoal res usedAxs timeout $
            defaultProof_status nGoal prName' $ configTimeLimit cfg
    in  (atpErr,
         cfg { proof_status = retval,
               resultOutput = output })
    where
      -- replace tabulators with each 8 spaces
      unTab = foldr (\ch li ->
                        if ch == '\x9' then "        "++li
                                       else ch:li) ""

{- |
  Maps the status message from MathServ results to GoalStatus.
  RegExp are used.
-}
mapToGoalStatus :: MWStatus -- ^ goal status
                -> GoalStatus -- ^ final parsed goal status
mapToGoalStatus stat = case (foStatus stat) of
        Theorem            -> Proved Nothing
        CounterSatisfiable -> Disproved
        _                  -> Open

{- |
  Gets the prover name from MathServResponse and extracts the name only
  (without version number). If the name's empty, prover name is "unknown".
-}
usedProverName :: String -- ^ Prover name from MathServResponse
               -> String -- ^ name without version number or unknown
usedProverName pn =
    if (null pn) then "unknown"
      else (takeWhile (\ch -> not $ ch == '_')) pn

{- |
  Default proof status. Contains the goal name, prover name
  and the time limit option used by MathServ.
-}
defaultProof_status :: AS_Anno.Named SPTerm -- ^ goal to prove
                    -> String -- ^ prover name
                    -> Int -- ^ time limit
                    -> Proof_status ()
defaultProof_status nGoal prName tl =
  (openProof_status (AS_Anno.senName nGoal)
                    prName ())
  {tacticScript = Tactic_script $ show tl}


{- |
  Returns the time limit from GenericConfig if available. Otherwise
  guiDefaultTimeLimit is returned.
-}
configTimeLimit :: GenericConfig ()
                -> Int
configTimeLimit cfg = 
    maybe (guiDefaultTimeLimit) id $ timeLimit cfg


{- |
  Returns the value of a prover run used in GUI (Success or
  TLimitExceeded), and the proof_status containing all prove
  information available.
-}
proof_stat :: AS_Anno.Named SPTerm -- ^ goal to prove
           -> GoalStatus -- ^ Nothing stands for prove error
           -> [String] -- ^ Used axioms in the proof
           -> Bool -- ^ Timeout status
           -> Proof_status () -- ^ default proof status
           -> (ATPRetval, Proof_status ())
           -- ^ General return value of a prover run, used in GUI.
           --   Detailed proof status if information is available.
proof_stat nGoal res usedAxs timeOut defaultPrStat
  | (res == Proved Nothing) =
      (ATPSuccess, defaultPrStat
       { goalStatus = Proved $ if elem (AS_Anno.senName nGoal) usedAxs
                               then Nothing
                               else Just False
       , usedAxioms = filter (/=(AS_Anno.senName nGoal)) usedAxs })
  | (res == Disproved) =
      (ATPSuccess, defaultPrStat { goalStatus = Disproved } )
  | timeOut =
      (ATPTLimitExceeded,
       defaultPrStat { goalStatus = res })
  | otherwise = (ATPSuccess, defaultPrStat { goalStatus = res })
