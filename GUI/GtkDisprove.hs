{- |
Module      :  $Header$
Description :  Gtk Module to enable disproving Theorems
Copyright   :  (c) Simon Ulbricht, Uni Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a disproving module that checks consistency of inverted
theorems.
-}

module GUI.GtkDisprove where

import Static.GTheory
import Static.DevGraph

import Proofs.AbstractState

import Common.ExtSign
import Common.Result
import Common.AS_Annotation
import Common.Utils (nubOrd)
import qualified Common.OrderedMap as OMap

import Comorphisms.LogicGraph

import GUI.GtkUtils

import Logic.Logic
import Logic.Prover
import Logic.Comorphism
import Logic.Coerce
import Logic.Grothendieck

import Data.List
import Data.Graph.Inductive.Graph

import System.Timeout

disproveThmSingle :: String -- ^ selected goal to disprove
                  -> String -- ^ selected prover
                  -> LNode DGNodeLab
                  -> Int -- ^ timeout limit
                  -> IO () -- ^ results are only displayed to the user.
disproveThmSingle selGoal selPr (_, lbl) t'' =
  let info s = infoDialog ("Disprove " ++ selGoal) s in
  case globalTheory lbl of
    Nothing -> info "Disprove failed: No global Theory"
    Just (G_theory lid1 (ExtSign sign symb) i1 sens i2) -> 
      case OMap.lookup selGoal sens of
        Nothing -> error "GtkDisprove.disproveThmSingle(1)"
        Just sen -> case negation lid1 $ sentence sen of
          Nothing -> info "Disprove failed: negation is not defined"
          Just s' -> do
            let negSen = sen { sentence = s', isAxiom = True }
                axs = OMap.filter isAxiom sens
                sens' = OMap.insert selGoal negSen axs
                g_th = G_theory lid1 (ExtSign sign symb) i1 sens' i2
                subL = sublogicOfTh g_th
                lcc = getConsCheckers $ findComorphismPaths logicGraph subL
            case find (\ (p, _) -> getPName p == selPr) lcc of
              Nothing -> 
                info $ "failed to find Consistency Checker for the selected prover\n\n"
                  ++ "possible ConsCheckers are:\n" ++ intercalate "\n" 
                   (nubOrd $ map (getPName . fst) lcc)
              Just (G_cons_checker lid4 cc, Comorphism cid) -> do
                let lidS = sourceLogic cid
                    lidT = targetLogic cid
                    res = do
                      bTh' <- coerceBasicTheory lid1 lidS "" (sign, toNamedList sens')
                      (sig2, sens2) <- wrapMapTheory cid bTh'
                      incl <- subsig_inclusion lidT (empty_signature lidT) sig2
                      return TheoryMorphism
                        { tSource = emptyTheory lidT
                        , tTarget = Theory sig2 $ toThSens sens2
                        , tMorphism = incl }
                case maybeResult res of
                  Nothing ->
                    info "Disprove failed: TheoryMorphism could not be constructed"
                  Just mor -> do
                    let thName = getDGNodeName lbl
                        t' = t'' * 1000000
                        ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
                    cc' <- coerceConsChecker lid4 lidT "" cc
                    ccS <- (if ccNeedsTimer cc' then timeout t' else ((return . Just) =<<))
                      (ccAutomatic cc' thName ts mor [])
                    case ccS of
                      Just ccStatus -> do
                           info $ "the ConsistencyChecker " ++ ccName cc' ++ " has returned "
                             ++ "the following " ++ case ccResult ccStatus of
                               Nothing -> ""
                               Just b -> if b then "consistent" else "inconsistent"
                             ++ " results:\n" ++ show (ccProofTree ccStatus)
                      Nothing -> do
                           info $ "the ConsistencyChecker has not returned any results\n"
                             ++ "ConsistencyChecker used: " ++ ccName cc'

