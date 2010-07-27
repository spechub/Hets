{- |
Module      :  $Header$
Description :  Gtk Module to enable disproving Theorems
Copyright   :  (c) Simon Ulbricht, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a disproving module that checks consistency of inverted
theorems.
-}

module GUI.GtkDisprove where

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Proofs.AbstractState

import Common.DocUtils (showDoc)
import Common.ExtSign
import Common.Result
import Common.AS_Annotation
import Common.OrderedMap as OMap

import Debug.Trace

import Logic.Logic
import Logic.Prover
import Logic.Comorphism
import Logic.Coerce

import Data.Graph.Inductive.Graph

import System.Timeout

 -- TODO use return value of consistencyCheck and mark node
 -- TODO implement in GtkProverGui

disproveNode :: Logic lid sublogics
                     basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree =>
              AnyComorphism -> String -> LNode DGNodeLab
             -> ProofState lid sentence -> Int -> IO (ProofState lid sentence)
disproveNode ac@(Comorphism cid) selGoal (_, lbl) state t'' = do
  case (fst . head) $ getConsCheckers [ac] of
    (G_cons_checker lid4 cc) ->
      let
        lidS = sourceLogic cid
        lidT = targetLogic cid
        thName = getDGNodeName lbl
        t = t'' * 1000000
        ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
      in case do
        (G_theory lid1 (ExtSign sign _) _ axs _) <- getGlobalTheory lbl
        let axs' = OMap.filter isAxiom axs
            negSen = case OMap.lookup selGoal axs of
                       Nothing -> error "GtkDisprove.disproveNode(1)"
                       Just sen ->
                         case negation lid1 $ sentence sen of
                           Nothing -> error "GtkDisprove.disproveNode(2)"
                           Just sen' -> sen { sentence = sen' }
            sens = toNamedList $ OMap.insert selGoal negSen axs'
        trace (showDoc sens "") $ return ()
        bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS "" (sign, sens)
        (sig2, sens2) <- wrapMapTheory cid bTh'
        incl <- subsig_inclusion lidT (empty_signature lidT) sig2
        return (sig1, TheoryMorphism
          { tSource = emptyTheory lidT
          , tTarget = Theory sig2 $ toThSens sens2
          , tMorphism = incl }) of
      Result _ Nothing -> return state -- node is not changed
      Result _ (Just (_, mor)) -> do
        cc' <- coerceConsChecker lid4 lidT "" cc
        putStrLn $ ccName cc'
        ccS <- (if ccNeedsTimer cc' then timeout t else ((return . Just) =<<))
          (ccAutomatic cc' thName ts mor [])
        case ccS of
                   Just ccStatus ->
                     case ccResult ccStatus of
                       Just b -> if b
                                 then let ps' = openProofStatus selGoal
                                            (ccName cc') (ccProofTree ccStatus)
                                          ps = ps' { goalStatus = Disproved }
                                   in do
                                   putStrLn "disprove successful"
                                   return $ markProved ac lidT [ps] state
                                 else return state
                       Nothing -> return state
                   Nothing -> return state


