{- |
Module      :  $Header$
Description :  Gtk GUI for the consistency checker
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the consistency checker.
-}

module GUI.GtkConsistencyChecker
  (showConsistencyChecker)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade
import Graphics.UI.Gtk.ModelView as MV

import GUI.GtkUtils
import qualified GUI.Glade.ConsistencyChecker as ConsistencyChecker
import GUI.GraphTypes

import Static.DevGraph
import Static.GTheory
import Static.DGTranslation (comSublogics)

import Interfaces.DataTypes

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism)

import Comorphisms.LogicGraph (logicGraph)

import Common.LibName (LIB_NAME)

import Proofs.AbstractState
import Proofs.InferBasic (consistencyCheck)

import Data.IORef
import Data.Graph.Inductive.Graph (LNode)

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> IO ()
showConsistencyChecker gInfo@(GInfo { libName = ln }) = postGUIAsync $ do
  xml            <- getGladeXML ConsistencyChecker.get
  -- get objects
  window         <- xmlGetWidget xml castToWindow "ConsistencyChecker"
  btnClose       <- xmlGetWidget xml castToButton "btnClose"
  -- get nodes view and buttons
  trvNodes       <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll    <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone   <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert <- xmlGetWidget xml castToButton "btnNodesInvert"
  -- get checker view and buttons
  --lblStatus      <- xmlGetWidget xml castToLabel "lblStatus"
  --lblSublogic    <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout      <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck       <- xmlGetWidget xml castToButton "btnCheck"
  btnStop        <- xmlGetWidget xml castToButton "btnStop"
  btnFineGrained <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder      <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"

  let widgets = [ toWidget trvFinder, toWidget btnCheck, toWidget btnFineGrained
                , toWidget btnStop, toWidget sbTimeout]

  -- get nodes
  (le, dg, nodes) <- do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> error "No state given."
      Just ist -> do
        let le = i_libEnv ist
            dg = lookupDGraph ln le
        return (le, dg, labNodesDG $ dg)

  -- setup data
  listNodes <- setListData trvNodes (\ (_,l) -> getDGNodeName l) nodes
  listFinder <- setListData trvFinder (\ (a,_) -> getPName a) []

  -- setup view selection actions
  setListSelectorSingle trvFinder $ return ()
  setListSelectorMultiple trvNodes btnNodesAll btnNodesNone btnNodesInvert
                          $ updateNodes trvNodes listNodes listFinder
                          (do listStoreClear listFinder; activate widgets False)
                          (activate widgets True)

  -- bindings
  onClicked btnClose $ widgetDestroy window
  onClicked btnFineGrained $ return ()
  onClicked btnStop $ return ()
  onClicked btnCheck $ do
    nodes' <- getNodes trvNodes listNodes
    finder <- getFinder trvFinder listFinder
    check ln le dg finder nodes'

  widgetShow window

-- | Get selected finder
getNodes :: TreeView -> ListStore (LNode DGNodeLab) -> IO [LNode DGNodeLab]
getNodes view list = do
  selector <- treeViewGetSelection view
  rows <- treeSelectionGetSelectedRows selector
  mapM (\ (row:[]) -> listStoreGetValue list row) rows

-- | Get selected nodes
getFinder :: TreeView -> ListStore (G_cons_checker, AnyComorphism)
          -> IO (G_cons_checker, AnyComorphism)
getFinder view list = do
  selector <- treeViewGetSelection view
  (Just model) <- treeViewGetModel view
  (Just iter) <- treeSelectionGetSelected selector
  (row:[]) <- treeModelGetPath model iter
  listStoreGetValue list row

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore (LNode DGNodeLab)
            -> ListStore (G_cons_checker, AnyComorphism) -> IO () -> IO ()
            -> IO ()
updateNodes view listNodes listFinder lock unlock = do
  nodes' <- getNodes view listNodes
  -- get list of theories
  let sublogics = map (sublogicOfTh . dgn_theory . snd) nodes'
  if sublogics == [] then lock
    else do
      maybe lock
        (\ sl -> do unlock; updateFinder listFinder sl)
        $ foldl (\ ma b -> case ma of
                  Just a -> comSublogics b a
                  Nothing -> Nothing) (Just $ head sublogics) $ tail sublogics

-- | Update the list of finder
updateFinder :: ListStore (G_cons_checker, AnyComorphism) -> G_sublogics
             -> IO ()
updateFinder list sublogic = do
  listStoreClear list
  mapM_ (listStoreAppend list) $ snd
    $ foldr (\ b@(a,_) c@(ns,bs) -> let n = getPName a in if elem n ns
                                    then c else (n:ns, b:bs)) ([],[])
    $ getConsCheckers $ findComorphismPaths logicGraph sublogic

activate :: [Widget] -> Bool -> IO ()
activate widgets active = do
  mapM_ (\ w -> widgetSetSensitive w active) widgets

check :: LIB_NAME -> LibEnv -> DGraph -> (G_cons_checker, AnyComorphism)
      -> [LNode DGNodeLab] -> IO ()
check ln le dg (cc, c) nodes = do
  mapM_ (consistencyCheck cc c ln le dg) nodes
