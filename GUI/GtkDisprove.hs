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

import GUI.GtkUtils as GtkUtils
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


-- TODO read current goalstatus properly during startup!
-- TODO (display results properly in the results window)
-- TODO better error dialogs!

-- TODO leave function with dialog if no goals are found

showDisproveGUI :: GInfo -> LibEnv -> DGraph -> LNode DGNodeLab -> IO ()
showDisproveGUI gi le dg (i,lbl) = case globalTheory lbl of
  Nothing -> error "GtkDisprove.showDisproveGUI"
  Just gt@(G_theory _ _ _ sens _) -> let
    fgoal g = let th = negate_th gt g
                  l = lbl { dgn_theory = th }
                  l' = l { globalTheory = computeLabelTheory le dg (i, l) }
                  no_cs = ConsistencyStatus CSUnchecked ""
                  stat = case OMap.lookup g sens of
                    Nothing -> no_cs
                    Just tm -> case thmStatus tm of
                      [] -> no_cs
                      ts -> basicProofToConStatus $ maximum $ map snd ts
              in FNode { name = g, node = (i,l'), sublogic = sublogicOfTh th,
                   cStatus = stat }
    fgoals = map fgoal $ OMap.keys $ OMap.filter (not . isAxiom) sens
    in do
      wait <- newEmptyMVar
      showDisproveWindow wait (libName gi) le dg gt fgoals
      res <- takeMVar wait
      runDisproveAtNode gi (i,lbl) res
      return ()

negate_th :: G_theory -> String -> G_theory
negate_th g_th goal = case g_th of
  G_theory lid1 (ExtSign sign symb) i1 sens i2 ->
      let axs = OMap.filter isAxiom sens
          negSen = case OMap.lookup goal sens of
                     Nothing -> error "GtkDisprove.negate_th(1)"
                     Just sen ->
                       case negation lid1 $ sentence sen of
                         -- TODO find proper way to face this error without crash!
                         Nothing -> error "GtkDisprove.negate_th(2)"
                         Just sen' -> sen { sentence = sen', isAxiom = True }
          sens' = OMap.insert goal negSen axs
      in G_theory lid1 (ExtSign sign symb) i1 sens' i2

disproveAtNode :: GInfo -> Int -> DGraph -> IO ()
disproveAtNode gInfo descr dgraph = do
  let iSt = intState gInfo
  ost <- readIORef iSt
  case i_state ost of
    Nothing -> return ()
    Just ist -> do
      let le = i_libEnv ist
          dgn = labDG dgraph descr
      showDisproveGUI gInfo le dgraph (descr, dgn)

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


-- | Displays a GUI to set TimeoutLimit and select the ConsistencyChecker
-- and holds the functionality to call the ConsistencyChecker for the
-- (previously negated) selected Theorems.

-- TODO proveAtNode anschauen, nach hasLock (..), tryLockLocal,
                     -- MVar auf LNode DGNodeLab

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
        mapM_ ( \ p@(row : []) -> do
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
      Nothing -> error "Consistency checker: internal error"
      Just (_, f) -> return f
    switch False
    tid <- forkIO $ do
      check inclThms ln le dg f timeout listGoals updat goals'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of consistency check" listGoals []
        signalBlock shN
        sortNodes trvGoals listGoals
        signalUnblock shN
        upd
        activate checkWidgets True
        pexit

  onDestroy window $ do
    fnodes' <- listStoreToList listGoals
    -- TODO face the case that no prover can be selected!
    Just (_, f) <- getSelectedSingle trvFinder listFinder
    case g_th of
      G_theory lid _s _i1 sens _i2 -> let
        sens' = foldr (\ fg t -> if (sType . cStatus) fg == CSConsistent
          then let
            n' = name fg
            es = Map.findWithDefault (error
                   "GtkDisprove.showDisproveWindow") n' t
            s = OMap.ele es
            ps = openProofStatus n' (fName f) (empty_proof_tree lid)
            bp = BasicProof lid ps { goalStatus = Disproved }
            c = comorphism f !! selected f
            s' = s { senAttr = ThmStatus $ (c, bp) : thmStatus s }
            in Map.insert n' es { OMap.ele = s' } t
          else t ) sens fnodes'
        in putMVar res $ return (G_theory lid _s _i1 sens' _i2)

  selectWith (== ConsistencyStatus CSUnchecked "") upd
  widgetShow window
