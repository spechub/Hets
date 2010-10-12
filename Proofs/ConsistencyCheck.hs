{- |
Module      :  $Header$
Description :  devGraph rule that calls consistency checker for specific logics
Copyright   :  (c) C. Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

devGraph rule that calls consistency checker for specific logics
-}

module Proofs.ConsistencyCheck
  ( consistencyCheck
  , SType (..)
  , ConsistencyStatus (..)
  , basicProofToConStatus
  ) where

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Proofs.AbstractState
import Proofs.FreeDefLinks

import Common.DocUtils (showDoc)
import Common.ExtSign
import Common.LibName
import Common.Result
import Common.AS_Annotation
import Common.Utils (timeoutSecs)

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Data.Graph.Inductive.Graph
import Data.Time.LocalTime (timeToTimeOfDay)
import Data.Time.Clock (secondsToDiffTime)
import Data.Ord (comparing)

data SType = CSUnchecked
           | CSTimeout
           | CSError
           | CSInconsistent
           | CSDisproved
           | CSConsistent
           deriving (Eq, Ord)

data ConsistencyStatus = ConsistencyStatus { sType :: SType
                                           , sMessage :: String }

instance Show ConsistencyStatus where
  show cs = case sType cs of
    CSUnchecked -> "Unchecked"
    _ -> sMessage cs

instance Eq ConsistencyStatus where
  (==) cs1 cs2 = compare cs1 cs2 == EQ

instance Ord ConsistencyStatus where
  compare = comparing sType

{- converts a GTheory.BasicProof to ConsistencyStatus.
The conversion is not exact, but sufficient since this function is only
implemented in GtkDisprove for proper display of goalstatus.
-}
basicProofToConStatus :: BasicProof -> ConsistencyStatus
basicProofToConStatus bp = ConsistencyStatus (basicProofToSType bp) ""

basicProofToSType :: BasicProof -> SType
basicProofToSType bp = case bp of
  BasicProof _ st -> case goalStatus st of
    Open _ -> CSUnchecked
    Disproved -> CSDisproved
    Proved c -> if c then CSConsistent else CSInconsistent
  _ -> CSConsistent

{- TODO instead of LibEnv.. get FreeDefs as Input. create wrapper that calcs
FreeDefs from LibEnv, DGraph and LibName (so that the call remains the same).
 -}

consistencyCheck :: Bool -> G_cons_checker -> AnyComorphism -> LibName -> LibEnv
                 -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus
consistencyCheck includeTheorems (G_cons_checker lid4 cc) (Comorphism cid) ln
  le dg (n', lbl) t'' = do
  let lidS = sourceLogic cid
      lidT = targetLogic cid
      thName = shows (getLibId ln) "_" ++ getDGNodeName lbl
      t' = timeToTimeOfDay $ secondsToDiffTime $ toInteger t''
      ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
      mTimeout = "No results within: " ++ show t'
  case do
        (G_theory lid1 (ExtSign sign _) _ axs _) <- getGlobalTheory lbl
        let namedSens = toNamedList axs
            sens = if includeTheorems then
              map (\ s -> s { isAxiom = True }) namedSens
              else namedSens
        bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS "" (sign, sens)
        (sig2, sens2) <- wrapMapTheory cid bTh'
        incl <- subsig_inclusion lidT (empty_signature lidT) sig2
        return (sig1, TheoryMorphism
          { tSource = emptyTheory lidT
          , tTarget = Theory sig2 $ toThSens sens2
          , tMorphism = incl }) of
    Result ds Nothing ->
      return $ ConsistencyStatus CSError $ unlines $ map diagString ds
    Result _ (Just (sig1, mor)) -> do
      cc' <- coerceConsChecker lid4 lidT "" cc
      ret <- (if ccNeedsTimer cc then timeoutSecs t''
              else ((return . Just) =<<))
        (ccAutomatic cc' thName ts mor $ getCFreeDefMorphs lidT le ln dg n')
      return $ case ret of
        Just ccStatus -> case ccResult ccStatus of
          Just b -> if b then let
            Result ds ms = extractModel cid sig1 $ ccProofTree ccStatus
            msgLines = map diagString ds ++ lines (show $ ccProofTree ccStatus)
            in case ms of
            Nothing -> ConsistencyStatus CSConsistent $ unlines
              ("consistent, but could not reconstruct a model" : msgLines)
            Just (sig3, sens3) -> let
              thTxt = showDoc
                (G_theory lidS (mkExtSign sig3) startSigId (toThSens sens3)
                        startThId) ""
              in ConsistencyStatus CSConsistent $
                 case filterDiags 2 ds of
                   [] -> thTxt
                   _ -> unlines $ lines thTxt ++ "%[" : msgLines ++ ["]%"]
            else ConsistencyStatus CSInconsistent $ show (ccProofTree ccStatus)
          Nothing -> if ccUsedTime ccStatus >= t' then
            ConsistencyStatus CSTimeout mTimeout
            else ConsistencyStatus CSError $ show (ccProofTree ccStatus)
        Nothing -> ConsistencyStatus CSTimeout mTimeout
