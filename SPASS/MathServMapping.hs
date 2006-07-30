{- |
Module      :  $Header$
Description :  Maps a MathServResponse into a prover configuration
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Maps a MathServResponse into a GenericConfig structure

-}

module SPASS.MathServMapping where

import qualified Common.AS_Annotation as AS_Anno

import Logic.Prover

import SPASS.MathServParsing
import SPASS.Sign

import Data.Maybe

import GUI.GenericATP (guiDefaultTimeLimit)
import GUI.GenericATPState

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
    either (\failure -> 
              (ATPError "MathServ Error:\n", -- first line of error message as second line
               cfg { proof_status = defaultProof_status nGoal
                       (prName ++ " [via MathServ]") (configTimeLimit cfg),
                    resultOutput = lines failure }
                    ))
              (\res -> mapProverResult res cfg nGoal prName)
              (foAtpResult msr)

--        mapProverResult (foAtpResult msr) cfg nGoal prName
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
        output = 
         -- system name if via Broker
         -- tstp proof with calculus
         -- time ressource global
            lines $ unTab $ outputStr atpResult
        timeout = (foAtpStatus $ systemStatus atpResult) == Unsolved Timeout
        
        -- get real prover name if Broker was used
        brokerName = "MSBroker" -- introduce String constant
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
mapToGoalStatus stat = case (foAtpStatus stat) of
        Solved Theorem            -> Proved Nothing
        Solved CounterSatisfiable -> Disproved
        _                         -> Open

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
-- !! TacticScript füllen:
{-
  format of tactic_script and parser for MathServBroker and 
    individual MathServ reasoners
-}
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
