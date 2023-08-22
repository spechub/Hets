{- |
Module      :  ./SoftFOL/MathServMapping.hs
Description :  Maps a MathServResponse into a prover configuration.
Copyright   :  (c) Rainer Grabbe
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Maps a MathServResponse into a GenericConfig structure.

-}

module SoftFOL.MathServMapping where

import Common.Doc -- as Pretty
import qualified Common.AS_Annotation as AS_Anno
import Common.ProofTree

import Logic.Prover

import SoftFOL.MathServParsing
import SoftFOL.Sign hiding (Theorem)

import Interfaces.GenericATPState

{- |
  Name of the prover if MathServ was called via Broker.
-}
brokerName :: String
brokerName = "MathServe Broker"

{- |
  Maps a MathServResponse record into a GenericConfig with ProofStatus.
  If an error occured, an ATPError with error message instead of result output
  will be returned.
-}
mapMathServResponse :: [String] -- ^ all axiom names
                    -> Either String MathServResponse
                    -- ^ SOAP faultstring or Parsed MathServ data
                    -> GenericConfig ProofTree -- ^ configuration to use
                    -> AS_Anno.Named SPTerm -- ^ goal to prove
                    -> String -- ^ prover name
                    -> (ATPRetval, GenericConfig ProofTree)
                    {- ^ (retval, configuration with proof status and
                    complete output) -}
mapMathServResponse axs eMsr cfg nGoal prName =
    either (\ errStr -> (ATPError errStr, cfg))
           (\ msr ->
            either
              (\ failure ->
                 (ATPError ("MathServe Error: " ++ case lines failure of
                   [] -> ""
                   h : _ -> h),
                 cfg { proofStatus = defaultProofStatus nGoal
                         (prName ++ " [via MathServe]") (configTimeLimit cfg)
                         (extraOpts cfg) "",
                       resultOutput = lines failure,
                       timeUsed = cpuTime $ timeResource msr }))
              (\ res -> mapProverResult axs res (timeResource msr)
                        cfg nGoal prName)
              (foAtpResult msr))
           eMsr

{- |
  Maps a FoAtpResult record into a GenericConfig with ProofStatus.
  Result output contains all important informations in a list of Strings.
  The function should only be called if there is a FoAtpResult available.
-}
mapProverResult :: [String] -- ^ all axiom names
                -> MWFoAtpResult -- ^ parsed FoATPResult data
                -> MWTimeResource -- ^ global time spent
                -> GenericConfig ProofTree -- ^ configuration to use
                -> AS_Anno.Named SPTerm -- ^ goal to prove
                -> String -- ^ prover name
                -> (ATPRetval, GenericConfig ProofTree)
                -- ^ (retval, configuration with proof status, complete output)
mapProverResult axs atpResult timeRes cfg nGoal prName =
    let sStat = systemStatus atpResult
        res = mapToGoalStatus sStat
        prf = proof atpResult
        output = (lines . show) $
          (if prName == brokerName then
              text "Used prover  " <+> colon <+> text
                           (usedProverName $ systemStr atpResult)
            else empty)
          $+$ text "Calculus     " <+> colon <+>
              text (show $ calculus prf)
          $+$ text "Spent time   " <+> colon <+> (
              text "CPU time       " <+> equals <+>
              text (show $ cpuTime timeRes)
              $+$ text "Wall clock time" <+> equals <+>
              text (show $ wallClockTime timeRes) )
          $+$ text "Prover output" <+> colon $+$
              vcat (map (fsep . map text . words) (lines $ outputStr atpResult))
          $+$ text (replicate 75 '-')
        timeout = foAtpStatus sStat == Unsolved Timeout

        -- get real prover name if Broker was used
        prName' = if prName == brokerName
                     then usedProverName (systemStr atpResult)
                          ++ " [via " ++ brokerName ++ "]"
                     else prName ++ " [via MathServe]"
        usedAxs = case axioms prf of
          [] -> [AS_Anno.senAttr nGoal]
          as -> words as
        (atpErr, retval) = proofStat axs nGoal res usedAxs timeout $
            defaultProofStatus nGoal prName'
                           (configTimeLimit cfg)
                           (extraOpts cfg)
                           (formalProof prf)
    in (atpErr,
         cfg { proofStatus = retval,
               resultOutput = output,
               timeUsed = cpuTime timeRes })

{- |
  Maps the status message from MathServ results to GoalStatus.
-}
mapToGoalStatus :: MWStatus -- ^ goal status
                -> GoalStatus -- ^ final parsed goal status
mapToGoalStatus stat = case foAtpStatus stat of
        Solved Theorem -> Proved True
        Solved CounterSatisfiable -> Disproved
        s -> Open $ Reason [show s]

{- |
  Gets the prover name from MathServResponse and extracts the name only
  (without version number). If the name's empty, prover name is "unknown".
-}
usedProverName :: String -- ^ Prover name from MathServResponse
               -> String -- ^ name without version number or unknown
usedProverName pn =
    if null pn then "unknown"
      else takeWhile (/= '_') pn

{- |
  Default proof status. Contains the goal name, prover name
  and the time limit option used by MathServ.
-}
defaultProofStatus :: AS_Anno.Named SPTerm -- ^ goal to prove
                    -> String -- ^ prover name
                    -> Int -- ^ time limit
                    -> [String] -- ^ list of used options
                    -> String -- ^ proof tree (simple text)
                    -> ProofStatus ProofTree
defaultProofStatus nGoal prName tl opts pt =
  (openProofStatus (AS_Anno.senAttr nGoal)
                    prName (ProofTree pt))
  {tacticScript = TacticScript $ show ATPTacticScript
    {tsTimeLimit = tl,
     tsExtraOpts = opts} }

{- |
  Returns the value of a prover run used in GUI (Success or
  TLimitExceeded), and the proofStatus containing all prove
  information available.
-}
proofStat :: [String] -- ^ all axiom names
           -> AS_Anno.Named SPTerm -- ^ goal to prove
           -> GoalStatus -- ^ Nothing stands for prove error
           -> [String] -- ^ Used axioms in the proof
           -> Bool -- ^ Timeout status
           -> ProofStatus ProofTree -- ^ default proof status
           -> (ATPRetval, ProofStatus ProofTree)
           {- ^ General return value of a prover run, used in GUI.
           Detailed proof status if information is available. -}
proofStat axs nGoal res usedAxs timeOut defaultPrStat = case res of
  Proved _ -> let nName = AS_Anno.senAttr nGoal in
      (ATPSuccess, defaultPrStat
       { goalStatus = Proved $ elem nName usedAxs
       , usedAxioms = case filter (/= nName) usedAxs of
          [] -> axs
          rs -> rs })
  _ -> (if timeOut then ATPTLimitExceeded else ATPSuccess
       , defaultPrStat { goalStatus = res })
