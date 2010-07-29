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

import Proofs.AbstractState

import Common.ExtSign
import Common.Result
import Common.AS_Annotation
import Common.OrderedMap as OMap

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

 -- TODO use return value of consistencyCheck and mark node
 -- TODO implement in GtkProverGui

disproveThmMultiple :: [String] -> LNode DGNodeLab -> ProofState lid sentence
                  -> Int -> IO (ProofState lid sentence)
disproveThmMultiple = undefined

disproveThmSingle :: Logic lid sublogics
                     basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree =>
                  String -> LNode DGNodeLab -> ProofState lid sentence
                  -> Int -> IO (ProofState lid sentence)
disproveThmSingle selGoal (_, lbl) state t'' =
  let info s = infoDialog ("Disprove " ++ selGoal) s in
  case globalTheory lbl of
    Nothing -> error "GtkDisprove.disproveThmSingle(0)"
    Just (G_theory lid1 (ExtSign sign symb) idx axs idx') -> do
      let axs' = OMap.filter isAxiom axs
          negSen = case OMap.lookup selGoal axs of
                     Nothing -> error "GtkDisprove.disproveThmSingle(1)"
                     Just sen ->
                       case negation lid1 $ sentence sen of
                         Nothing -> error "GtkDisprove.disproveThmSingle(2)"
                         Just sen' -> sen { sentence = sen', isAxiom = True }
          sens = OMap.insert selGoal negSen axs'
          lSen = toNamedList sens
          subL = sublogicOfTh (G_theory lid1 (ExtSign sign symb) idx sens idx')
          lcc = getConsCheckers $ findComorphismPaths logicGraph subL
      case selectConsChecker "darwin" lcc of
        Nothing -> do
          info "failed to find Consistency Checker for inverted theorem"
          return state
        Just (G_cons_checker lid4 cc, cm@(Comorphism cid)) -> do
          let lidS = sourceLogic cid
              lidT = targetLogic cid
          case do
            bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS "" (sign, lSen)
            (sig2, sens2) <- wrapMapTheory cid bTh'
            incl <- subsig_inclusion lidT (empty_signature lidT) sig2
            return (sig1, TheoryMorphism
               { tSource = emptyTheory lidT
               , tTarget = Theory sig2 $ toThSens sens2
               , tMorphism = incl }) of
            Result _ Nothing -> do
              info "Error: could not construct TheoryMorphism"
              return state -- node is not changed
            Result _ (Just (_, mor)) -> do
                let thName = getDGNodeName lbl
                    t' = t'' * 1000000
                    ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
                cc' <- coerceConsChecker lid4 lidT "" cc
                putStrLn $ "[Using ConsChecker:] " ++ ccName cc'
                ccS <- (if ccNeedsTimer cc' then timeout t' else ((return . Just) =<<))
                  (ccAutomatic cc' thName ts mor [])
                case ccS of
                  Just ccStatus ->
                    case ccResult ccStatus of
                      Just b -> if b
                                then let ps' = openProofStatus selGoal
                                            (ccName cc') (ccProofTree ccStatus)
                                         ps = ps' { goalStatus = Disproved }
                                     in do
                                   info "Goal has been disproved!"
                                   return $ markProved cm lidT [ps] state
                                else do
                                   info "Goal could not be disproved(1)!"
                                   return state
                      Nothing -> do
                               info "Goal could not be disproved(2)!"
                               return state
                  Nothing -> do
                           info "Goal could not be disproved(3)!"
                           return state


selectConsChecker :: String -> [(G_cons_checker, AnyComorphism)] 
                  -> Maybe (G_cons_checker, AnyComorphism)
selectConsChecker _ [] = Nothing
selectConsChecker s cc = case find (\ (c,_) -> getPName c == s) cc of
                            Nothing -> Just $ head cc
                            Just cc' -> Just cc' 
