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

{-
showDisprove :: LNode DGNodeLab -> ProofState lid sentence -> String
             -> IO (ProofState lid sentence)
showDisprove (i, lbl) state selGoal =
  -- construct new G_theory containing the negated theorem
  -- as well as a list of suitable ConsCheckers and Comorphisms
  case globalTheory lbl of
    Nothing -> error "GtkDisprove.showDisprove"
    Just (G_theory lid1 (ExtSign sign symb) i1 sens i2) -> do
      let axs = OMap.filter isAxiom sens
          negSen = case OMap.lookup selGoal sens of
                     Nothing -> error "GtkDisprove.disproveThmSingle(1)"
                     Just sen ->
                       case negation lid1 $ sentence sen of
                         Nothing -> error "GtkDisprove.disproveThmSingle(2)"
                         Just sen' -> sen { sentence = sen', isAxiom = True }
          sens' = OMap.insert selGoal negSen axs
          g_th = G_theory lid1 (ExtSign sign symb) i1 sens' i2
          subL = sublogicOfTh g_th
          lcc = getConsCheckers $ findComorphismPaths logicGraph subL
      -- new G_theory and ConsCheckers are passed on to the GUI
      -- results, if any, will be stored in MVar as a sideeffect
      wait <- newEmptyMVar
      showDisproveWindow g_th state selGoal lcc wait
      st' <- takeMVar wait
      return $ Result [] $ Just st'

-- | Displays a GUI to set TimeoutLimit and select the ConsistencyChecker
-- and holds the functionality to call the ConsistencyChecker for the
-- single, previously selected Theorem.

-- TODO the NodeChecker GUI has been used to set the parameters, even though
-- it is not quite suitable for a single theorem only.
-- a new, simpler GUI should be designed, and the results should be displayed
-- instantly after the check
showDisproveWindow :: G_theory -> ProofState lid sentence -> String
                   -> [G_cons_checker, AnyComorphism] 
                   -> MVar (ProofState lid sentence) -> IO ()
showProverWindow g_th st selGoal listCons res = postGUIAsync $ do
  xml               <- getGladeXML ConsistencyChecker.get
  -- get objects
  window            <- xmlGetWidget xml castToWindow "NodeChecker"
  btnClose          <- xmlGetWidget xml castToButton "btnClose"
  btnResults         <- xmlGetWidget xml castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes          <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll       <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone      <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert    <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout   <- xmlGetWidget xml castToButton "btnNodesTimeout"
  cbInclThms        <- xmlGetWidget xml castToCheckButton "cbInclThms"
  -- get checker view and buttons
  cbComorphism      <- xmlGetWidget xml castToComboBox "cbComorphism"
  lblSublogic       <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout         <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck          <- xmlGetWidget xml castToButton "btnCheck"
  btnStop           <- xmlGetWidget xml castToButton "btnStop"
  -- btnFineGrained    <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder         <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Disprove"
  spinButtonSetValue sbTimeout $ fromIntegral guiDefaultTimeLimit

  let widgets = [ toWidget sbTimeout
                , toWidget cbComorphism
                , toWidget lblSublogic ]
      checkWidgets = widgets ++ [ toWidget btnClose
                                , toWidget btnNodesAll
                                , toWidget btnNodesNone
                                , toWidget btnNodesInvert
                                , toWidget btnNodesUnchecked
                                , toWidget btnNodesTimeout
                                , toWidget btnResults ]
      switch b = do
        widgetSetSensitive btnStop $ not b
        widgetSetSensitive btnCheck b

  toggleButtonSetActive cbInclThms False

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait     <- newEmptyMVar
  mView    <- newEmptyMVar

  -- setup data
  listNodes  <- setListData trvNodes id [selGoal]
  listFinder <- setListData trvFinder (getPName . fst) listCons

  -- setup comorphism combobox
  comboBoxSetModelText cbComorphism
  shC <- after cbComorphism changed
    $ setSelectedComorphism trvFinder listFinder cbComorphism

  -- setup view selection actions
  let update = do
        mf <- getSelectedSingle trvFinder listFinder
        updateComorphism trvFinder listFinder cbComorphism shC
        widgetSetSensitive btnCheck $ isJust mf
  setListSelectorSingle trvFinder update

  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    t'' <- spinButtonGetValueAsInt sbTimeout
    let (G_cons_checker lid4 cc, cm@(Comorphism cid)) = 
          getSelectedSingle trvFinder listFinder
        -- when the comorphism is known, a TheoryMorphism can be created
        -- and later be sent to the ConsistencyChecker
        getTheoryMorphism = 
          case g_th of
            G_theory lid1 (ExtSign sign symb) _ sens _ -> case do
              let listsens = toNamedList sens
                  lidS = sourceLogic cid
                  lidT = targetLogic cid
              bTh' <- coerceBasicTheory lid1 lidS "" (sign, listsens)
              (sig2, sens2) <- wrapMapTheory cid bTh'
              incl <- subsig_inclusion lidT (empty_signature lidT) sig2
              return $ TheoryMorphism
                 { tSource = emptyTheory lidT
                 , tTarget = Theory sig2 $ toThSens sens2
                 , tMorphism = incl } of
                Result _ Nothing -> Nothing
                Result _ (Just mor) -> Just mor
    case getTheoryMorphism of
      Nothing -> do
              info "Error: could not construct TheoryMorphism"
              return state -- node is not changed
      Just mor -> do
                let thName = getDGNodeName lbl
                    t' = t'' * 1000000
                    ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
                cc' <- coerceConsChecker lid4 lidT "" cc
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



  onDestroy window $ do
    putMVar res

setSelectedComorphism :: TreeView -> ListStore (G_cons_checker, AnyComorphism)
                      -> ComboBox -> IO ()
setSelectedComorphism view list cbComorphism = do
  mfinder <- getSelectedSingle view list
  case mfinder of
    Just (i, f) -> do
      sel <- comboBoxGetActive cbComorphism
      listStoreSetValue list i f { selected = sel }
    Nothing -> return ()

-}


disproveThmSingle :: Logic lid sublogics
                     basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree =>
                  String -- ^ selected goal to disprove
                  -> String -- ^ selected prover
                  -> LNode DGNodeLab
                  -> ProofState lid sentence -- ^ nodes current ProofState
                  -> Int -- ^ timeout limit
                  -> IO (ProofState lid sentence) -- ^ ProofState containing the results
disproveThmSingle selGoal selPr (_, lbl) state t'' =
  let info s = infoDialog ("Disprove " ++ selGoal) s in
  case globalTheory lbl of
    Nothing -> error "GtkDisprove.disproveThmSingle(0)"
    Just (G_theory lid1 (ExtSign sign symb) i1 sens i2) -> do
      let axs = OMap.filter isAxiom sens
          negSen = case OMap.lookup selGoal sens of
                     Nothing -> error "GtkDisprove.disproveThmSingle(1)"
                     Just sen ->
                       case negation lid1 $ sentence sen of
                         Nothing -> error "GtkDisprove.disproveThmSingle(2)"
                         Just sen' -> sen { sentence = sen', isAxiom = True }
          sens' = OMap.insert selGoal negSen axs
          g_th = G_theory lid1 (ExtSign sign symb) i1 sens' i2
          subL = sublogicOfTh g_th
          lcc = getConsCheckers $ findComorphismPaths logicGraph subL
      case selectConsChecker selPr lcc of
        Nothing -> do
          info "failed to find Consistency Checker for inverted theorem"
          return state
        Just (G_cons_checker lid4 cc, cm@(Comorphism cid)) -> do
          let lidS = sourceLogic cid
              lidT = targetLogic cid
          case do
            bTh'@(sig1, _) <- coerceBasicTheory lid1 lidS "" (sign, toNamedList sens')
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
selectConsChecker s cc = case cc of
  [] -> Nothing
  h : _ -> case find (\ (c,_) -> getPName c == s) cc of
                            Nothing -> Just h
                            Just c' -> Just c'
