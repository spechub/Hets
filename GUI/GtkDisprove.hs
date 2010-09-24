{- |
Module      :  $Header$
Description :  Gtk Module to enable disproving Theorems
Copyright   :  (c) Simon Ulbricht, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a disproving module that checks consistency of inverted
theorems.
-}

module GUI.GtkDisprove (showDisproveGUI) where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils as GtkUtils
import qualified GUI.Glade.NodeChecker as ConsistencyChecker
import GUI.GraphTypes

import Static.DevGraph
import Static.PrintDevGraph ()
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Interfaces.GenericATPState (guiDefaultTimeLimit)

import Logic.Logic
import Logic.Coerce
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover

import Comorphisms.LogicGraph (logicGraph)
import Comorphisms.KnownProvers

import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.LibName (LibName)
import Common.Result
import Common.ExtSign
import Common.Utils

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar

import Proofs.AbstractState

import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List
import Data.Maybe

import Proofs.ConsistencyCheck
import GUI.GtkConsistencyChecker
                   
showDisproveGUI :: GInfo -> LibEnv -> DGraph -> LNode DGNodeLab -> IO ()
showDisproveGUI gi le dg (i,lbl) = case globalTheory lbl of
  Nothing -> error "GtkDisprove.showDisproveGUI"
  Just gt@(G_theory lid1 (ExtSign sign symb) _ sens _) -> let
    fgoal g = let th = negate_th gt g 
                  n' = (i, lbl { dgn_theory = th })
              in FNode { name = g, node = n', sublogic = sublogicOfTh th,
                   cStatus = ConsistencyStatus CSUnchecked "" }
    fgoals = map fgoal $ OMap.keys $ OMap.filter (not . isAxiom) sens
    in do
      showDisproveWindow gi le dg gt fgoals

negate_th :: G_theory -> String -> G_theory
negate_th g_th goal = case g_th of
  G_theory lid1 (ExtSign sign symb) i1 sens i2 ->
      let axs = OMap.filter isAxiom sens
          negSen = case OMap.lookup goal sens of
                     Nothing -> error "GtkDisprove.disproveThmSingle(1)"
                     Just sen ->
                       case negation lid1 $ sentence sen of
                         Nothing -> error "GtkDisprove.disproveThmSingle(2)"
                         Just sen' -> sen { sentence = sen', isAxiom = True }
          sens' = OMap.insert goal negSen axs
      in G_theory lid1 (ExtSign sign symb) i1 sens' i2



-- | Displays a GUI to set TimeoutLimit and select the ConsistencyChecker
-- and holds the functionality to call the ConsistencyChecker for the
-- (previously negated) selected Theorems.

showDisproveWindow :: GInfo -> LibEnv -> DGraph -> G_theory -> [FNode] -> IO ()
showDisproveWindow gi le dg g_th fgoals = postGUIAsync $ do
  xml <- getGladeXML ConsistencyChecker.get
  -- get objects
  window <- xmlGetWidget xml castToWindow "NodeChecker"
  btnClose <- xmlGetWidget xml castToButton "btnClose"
  btnResults <- xmlGetWidget xml castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout <- xmlGetWidget xml castToButton "btnNodesTimeout"
  cbInclThms <- xmlGetWidget xml castToCheckButton "cbInclThms"
  -- get checker view and buttons
  cbComorphism <- xmlGetWidget xml castToComboBox "cbComorphism"
  lblSublogic <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck <- xmlGetWidget xml castToButton "btnCheck"
  btnStop <- xmlGetWidget xml castToButton "btnStop"
  trvFinder <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"
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

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait <- newEmptyMVar
  mView <- newEmptyMVar

  -- setup data
  listNodes <- setListData trvNodes show $ sort fgoals
  listFinder <- setListData trvFinder fName []

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

  let upd = updateNodes trvNodes listNodes
        (\ b s -> do
           labelSetLabel lblSublogic $ show s
           updateFinder trvFinder listFinder b s)
        (do
          labelSetLabel lblSublogic "No sublogic"
          listStoreClear listFinder
          activate widgets False
          widgetSetSensitive btnCheck False)
        (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings
  let selectWithAux f u = do
        signalBlock shN
        sel <- treeViewGetSelection trvNodes
        treeSelectionSelectAll sel
        rs <- treeSelectionGetSelectedRows sel
        mapM_ ( \ p@(row : []) -> do
          fn <- listStoreGetValue listNodes row
          (if f fn then treeSelectionSelectPath else treeSelectionUnselectPath)
            sel p) rs
        signalUnblock shN
        u
      selectWith f = selectWithAux $ f . cStatus

  onClicked btnNodesUnchecked
    $ selectWith (== ConsistencyStatus CSUnchecked "") upd
  onClicked btnNodesTimeout $ selectWith (== ConsistencyStatus CSTimeout "") upd

  onClicked btnResults $ showModelView mView "Models" listNodes []
  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    inclThms <- toggleButtonGetActive cbInclThms
    (updat, pexit) <- progressBar "Checking consistency" "please wait..."
    nodes' <- getSelectedMultiple trvNodes listNodes
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Consistency checker: internal error"
      Just (_, f) -> return f
    switch False
    tid <- forkIO $ do
      --check inclThms ln le dg f timeout listNodes updat nodes'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of consistency check" listNodes []
        signalBlock shN
        sortNodes trvNodes listNodes
        signalUnblock shN
        upd
        activate checkWidgets True
        pexit

{-  onDestroy window $ do
    nodes' <- listStoreToList listNodes
    let changes = foldl (\ cs (FNode { node = (i, l), cStatus = s }) ->
                      if (\ st -> st /= CSConsistent && st /= CSInconsistent)
                         $ sType s then cs
                        else
                          let n = (i, if sType s == CSInconsistent then
                                        markNodeInconsistent "" l
                                        else markNodeConsistent "" l)
                          in SetNodeLab l n : cs
                    ) [] nodes'
        dg' = changesDGH dg changes
    putMVar res $ Map.insert ln (groupHistory dg (DGRule "Consistency") dg') le
-}
  selectWith (== ConsistencyStatus CSUnchecked "") upd
  widgetShow window

disproveThmSingle :: FNode
                  -> Finder
                  -> Int -- ^ timeout limit
                  -> ProofState lid sentence
                  -> IO (ProofState lid sentence)
disproveThmSingle fgoal fdr t'' state = undefined {-
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
                        ts = TacticScript $ if ccNeedsTimer cc then "" else show t''
                    cc' <- coerceConsChecker lid4 lidT "" cc
                    ccS <- (if ccNeedsTimer cc' then timeoutSecs t'' else ((return . Just) =<<))
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
-}
