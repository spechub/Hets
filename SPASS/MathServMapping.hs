{- |
Module      :  $Header$
Description :  Maps a MathServResponse into a prover configuration.
Copyright   :  (c) Rainer Grabbe
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Maps a MathServResponse into a GenericConfig structure.

-}

module SPASS.MathServMapping where

import Common.Doc -- as Pretty
import qualified Common.AS_Annotation as AS_Anno

import Logic.Prover

import SPASS.MathServParsing
import SPASS.ProverState (configTimeLimit)
import SPASS.Sign

import Data.Maybe

import GUI.GenericATPState

{- |
  Name of the prover if MathServ was called via Broker.
-}
brokerName :: String
brokerName = "MSBroker"

{- |
  Maps a MathServResponse record into a GenericConfig with Proof_status.
  If an error occured, an ATPError with error message instead of result output
  will be returned.
-}
mapMathServResponse :: Either String MathServResponse 
                  -- ^ SOAP faultstring or Parsed MathServ data
                    -> GenericConfig String -- ^ configuration to use
                    -> AS_Anno.Named SPTerm -- ^ goal to prove
                    -> String -- ^ prover name
                    -> (ATPRetval, GenericConfig String)
                    -- ^ (retval, configuration with proof status and
                    --    complete output)
mapMathServResponse eMsr cfg nGoal prName =
    either (\ errStr -> (ATPError errStr,cfg))
           (\msr -> 
            either 
              (\failure -> 
                (ATPError ("MathServ Error: " ++
                   if (null failure) then [] else head $ lines failure),
                 cfg { proof_status = defaultProof_status nGoal
                         (prName ++ " [via MathServ]") (configTimeLimit cfg)
                         (extraOpts cfg) "",
                       resultOutput = lines failure,
                       timeUsed = globalTime $ timeResource msr }))
              (\res -> mapProverResult res (timeResource msr) cfg nGoal prName)
              (foAtpResult msr))
           eMsr

{- |
  Maps a FoAtpResult record into a GenericConfig with Proof_status.
  Result output contains all important informations in a list of Strings.
  The function should only be called if there is a FoAtpResult available.
-}
mapProverResult :: MWFoAtpResult -- ^ parsed FoATPResult data
                -> MWTimeResource -- ^ global time spent
                -> GenericConfig String -- ^ configuration to use
                -> AS_Anno.Named SPTerm -- ^ goal to prove
                -> String -- ^ prover name
                -> (ATPRetval, GenericConfig String)
                -- ^ (retval, configuration with proof status, complete output)
mapProverResult atpResult timeRes cfg nGoal prName =
    let res = mapToGoalStatus $ systemStatus atpResult
        output = (lines . show) $
          (if (prName == brokerName) then
              text "Used prover  " <+> colon <+> text
                           (usedProverName $ systemStr atpResult)
            else empty)
          $+$ text "Calculus     " <+> colon <+>
              text (show $ calculus $ proof atpResult)
          $+$ text "Spent time   " <+> colon <+> (
              text "CPU time       "              <+> equals <+>
              text (show $ cpuTime timeRes)       <+> text "ms"
              $+$ text "Wall clock time"          <+> equals <+>
              text (show $ wallClockTime timeRes) <+> text "ms" )
          $+$ text "Prover output" <+> colon $+$
              vcat (map text (lines $ unTab $ outputStr atpResult))
          $+$ text (replicate 75 '-')
        timeout = (foAtpStatus $ systemStatus atpResult) == Unsolved Timeout

        -- get real prover name if Broker was used
        prName' = if (prName == brokerName)
                     then (usedProverName $ systemStr atpResult)
                          ++ " [via MathServBroker]"
                     else prName ++ " [via MathServ]"
        usedAxs = if (null $ axioms $ proof atpResult)
                    then [AS_Anno.senName nGoal]
                    else words $ axioms $ proof atpResult
        (atpErr, retval) = proof_stat nGoal res usedAxs timeout $
            defaultProof_status nGoal prName'
                           (configTimeLimit cfg)
                           (extraOpts cfg)
                           (formalProof $ proof atpResult)
    in  (atpErr,
         cfg { proof_status = retval,
               resultOutput = output,
               timeUsed     = globalTime timeRes })
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
                    -> [String] -- ^ list of used options
                    -> String -- ^ proof tree
                    -> Proof_status String
defaultProof_status nGoal prName tl opts pt =
  (openProof_status (AS_Anno.senName nGoal)
                    prName pt)
  {tacticScript = Tactic_script
    {ts_timeLimit = tl,
     ts_extraOpts = unwords opts} }

{- |
  Returns the value of a prover run used in GUI (Success or
  TLimitExceeded), and the proof_status containing all prove
  information available.
-}
proof_stat :: AS_Anno.Named SPTerm -- ^ goal to prove
           -> GoalStatus -- ^ Nothing stands for prove error
           -> [String] -- ^ Used axioms in the proof
           -> Bool -- ^ Timeout status
           -> Proof_status String -- ^ default proof status
           -> (ATPRetval, Proof_status String)
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

{- |
  Sum over CPU time and wall clock time from a given MWTimeResource.
-}
globalTime :: MWTimeResource -- ^ time resource: CPU time, wall clock time
           -> Int -- ^ sum of both times
globalTime msr = (cpuTime msr) + (wallClockTime msr)
