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

module GUI.GtkDisprove (disproveAtNode) where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.NodeChecker as ConsistencyChecker
import GUI.GraphTypes
import GUI.GraphLogic hiding (openProofStatus)
import GUI.GtkConsistencyChecker

import Proofs.ConsistencyCheck

import Interfaces.GenericATPState (guiDefaultTimeLimit)
import Interfaces.DataTypes
import Interfaces.Utils (updateNodeProof)

import Logic.Logic
import Logic.Prover

import Static.DevGraph
import Static.GTheory
import Static.ComputeTheory

import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.LibName (LibName)
import Common.Result
import Common.ExtSign

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Monad (unless)

import Data.Graph.Inductive.Graph (LNode)
import Data.IORef
import qualified Data.Map as Map
import Data.List
import Data.Maybe

{- | this method holds the functionality to convert the nodes goals to the
FNode datatype from GUI.GtkConsistencyChecker. The goals are being negated
by negate_th and this theory is stored in FNodes DGNodeLab local and global
theory. -}
showDisproveGUI :: GInfo -> LibEnv -> DGraph -> LNode DGNodeLab -> IO ()
showDisproveGUI gi le dg (i, lbl) = case globalTheory lbl of
  Nothing -> error "GtkDisprove.showDisproveGUI(no global theory found)"
  Just gt@(G_theory _ _ _ _ sens _) -> let
    fg g th = let
      l = lbl { dgn_theory = th }
      l' = l { globalTheory = computeLabelTheory le dg (i, l) }
      no_cs = ConsistencyStatus CSUnchecked ""
      stat = case OMap.lookup g sens of
        Nothing -> no_cs
        Just tm -> case thmStatus tm of
          [] -> no_cs
          ts -> basicProofToConStatus $ maximum $ map snd ts
      in FNode { name = g, node = (i, l'), sublogic = sublogicOfTh th,
                 cStatus = stat }
    fgoals = foldr (\ (g, _) t -> case negate_th gt g of
      Nothing -> t
      Just nt -> fg g nt : t) []
        $ getThGoals gt
    in if null fgoals
      then
          errorDialogExt "Error (disprove)" "found no goals suitable for disprove function"
      else do
        wait <- newEmptyMVar
        showDisproveWindow wait (libName gi) le dg gt fgoals
        res <- takeMVar wait
        runDisproveAtNode gi (i, lbl) res

{- | negates a single sentence within a G_theory and returns a theory
containing all axioms in addition to the one negated sentence. -}
negate_th :: G_theory -> String -> Maybe G_theory
negate_th g_th goal = case g_th of
  G_theory lid1 syn (ExtSign sign symb) i1 sens _ ->
    case OMap.lookup goal sens of
      Nothing -> Nothing
      Just sen ->
        case negation lid1 $ sentence sen of
          Nothing -> Nothing
          Just sen' -> let
            negSen = sen { sentence = sen', isAxiom = True }
            sens' = OMap.insert goal negSen $ OMap.filter isAxiom sens
            in Just $ G_theory lid1 syn (ExtSign sign symb) i1 sens' startThId

{- | this function is being called from outside and manages the locking-
mechanism of the node being called upon. -}
disproveAtNode :: GInfo -> Int -> DGraph -> IO ()
disproveAtNode gInfo descr dgraph = do
  lockedEnv <- ensureLockAtNode gInfo descr dgraph
  case lockedEnv of
    Nothing -> return ()
    Just (dg, lbl, le) -> do
      acquired <- tryLockLocal lbl
      if acquired then do
      showDisproveGUI gInfo le dg (descr, lbl)
      unlockLocal lbl
      else errorDialogExt "Error" "Proof or disproof window already open"

{- | after results have been collected, this function is called to store
the results for this node within the dgraphs history. -}
runDisproveAtNode :: GInfo -> LNode DGNodeLab -> Result G_theory -> IO ()
runDisproveAtNode gInfo (v, dgnode) (Result ds mres) = case mres of
  Just rTh ->
    let oldTh = dgn_theory dgnode in
    unless (rTh == oldTh) $ do
      showDiagMessAux 2 ds
      lockGlobal gInfo
      let ln = libName gInfo
          iSt = intState gInfo
      ost <- readIORef iSt
      let (ost', hist) = updateNodeProof ln ost (v, dgnode) rTh
      case i_state ost' of
        Nothing -> return ()
        Just _ -> do
          writeIORef iSt ost'
          runAndLock gInfo $ updateGraph gInfo hist
      unlockGlobal gInfo
  _ -> return ()

{- | Displays a GUI to set TimeoutLimit and select the ConsistencyChecker
and holds the functionality to call the ConsistencyChecker for the
(previously negated) selected Theorems. -}
showDisproveWindow :: MVar (Result G_theory) -> LibName -> LibEnv
                   -> DGraph -> G_theory -> [FNode] -> IO ()
showDisproveWindow res ln le dg g_th fgoals = postGUIAsync $ do
  xml <- getGladeXML ConsistencyChecker.get
  -- get objects
  window <- xmlGetWidget xml castToWindow "NodeChecker"
  btnClose <- xmlGetWidget xml castToButton "btnClose"
  btnResults <- xmlGetWidget xml castToButton "btnResults"
  -- get goals view and buttons
  trvGoals <- xmlGetWidget xml castToTreeView "trvNodes"
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
  toolLabel <- xmlGetWidget xml castToLabel "label1"
  labelSetLabel toolLabel "Pick disprover"
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

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait <- newEmptyMVar
  mView <- newEmptyMVar

  -- setup data
  listGoals <- setListData trvGoals show $ sort fgoals
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

  let upd = updateNodes trvGoals listGoals
        (\ b s -> do
           labelSetLabel lblSublogic $ show s
           updateFinder trvFinder listFinder b s)
        (do
          labelSetLabel lblSublogic "No sublogic"
          listStoreClear listFinder
          activate widgets False
          widgetSetSensitive btnCheck False)
        (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvGoals btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings
  let selectWithAux f u = do
        signalBlock shN
        sel <- treeViewGetSelection trvGoals
        treeSelectionSelectAll sel
        rs <- treeSelectionGetSelectedRows sel
        mapM_ ( \ ~p@(row : []) -> do
          fn <- listStoreGetValue listGoals row
          (if f fn then treeSelectionSelectPath else treeSelectionUnselectPath)
            sel p) rs
        signalUnblock shN
        u
      selectWith f = selectWithAux $ f . cStatus

  onClicked btnNodesUnchecked
    $ selectWith (== ConsistencyStatus CSUnchecked "") upd
  onClicked btnNodesTimeout $ selectWith (== ConsistencyStatus CSTimeout "") upd

  onClicked btnResults $ showModelView mView "Models" listGoals []
  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    inclThms <- toggleButtonGetActive cbInclThms
    (updat, pexit) <- progressBar "Checking consistency" "please wait..."
    goals' <- getSelectedMultiple trvGoals listGoals
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Disprove: internal error"
      Just (_, f) -> return f
    switch False
    tid <- forkIO $ do
      {- call the check function from GUI.GtkConsistencyChecker.
      first argument means disprove-mode and leads the ConsistencyChecker
      to mark consistent sentences as disproved (since consistent with
      negated sentence) -}
      check True inclThms ln le dg f timeout listGoals updat goals'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of disproving" listGoals []
        signalBlock shN
        sortNodes trvGoals listGoals
        signalUnblock shN
        upd
        activate checkWidgets True
        pexit

  {- after window closes a new G_theory is created containing the results.
  only successful disprove attempts are returned; for each one, a new
  BasicProof is created and set to disproved. -}
  onDestroy window $ do
    fnodes' <- listStoreToList listGoals
    maybe_F <- getSelectedSingle trvFinder listFinder
    case maybe_F of
      Just (_, f) -> case g_th of
        G_theory lid syn sig i1 sens _ -> let
          sens' = foldr (\ fg t -> if (sType . cStatus) fg == CSInconsistent
            then let
              n' = name fg
              es = Map.findWithDefault (error
                   "GtkDisprove.showDisproveWindow") n' t
              s = OMap.ele es
              ps = openProofStatus n' (fName f) (empty_proof_tree lid)
              bp = BasicProof lid ps { goalStatus = Disproved }
              c = comorphism f !! selected f
              s' = s { senAttr = ThmStatus $ (c, bp) : thmStatus s } in
              Map.insert n' es { OMap.ele = s' } t
            else t ) sens fnodes'
          in putMVar res $ return (G_theory lid syn sig i1 sens' startThId)
      _ -> putMVar res $ return g_th

  selectWith (== ConsistencyStatus CSUnchecked "") upd
  widgetShow window
