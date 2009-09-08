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

import Interfaces.DataTypes

import Logic.Grothendieck

import Comorphisms.LogicGraph(logicGraph)

import Proofs.AbstractState (getConsCheckers, getPName)

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
  btnCheck       <- xmlGetWidget xml castToButton "btnCheck"
  btnStop        <- xmlGetWidget xml castToButton "btnStop"
  btnFineGrained <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder      <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"

  -- get nodes
  nodes <- do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> error "No state given."
      Just ist -> return $ labNodesDG $ lookupDGraph ln $ i_libEnv ist

  -- setup data
  listNodes <- setListData trvNodes (\ (_,l) -> getDGNodeName l) nodes
  listFinder <- setListData trvFinder id []

  -- setup view selection actions
  setListSelectorSingle trvFinder $ return ()
  setListSelectorMultiple trvNodes btnNodesAll btnNodesNone btnNodesInvert
                          $ updateNodes trvNodes listNodes listFinder

  -- bindings
  onClicked btnClose $ widgetDestroy window
  onClicked btnFineGrained $ return ()
  onClicked btnStop $ return ()
  onClicked btnCheck $ return ()

  widgetShow window

-- | Get selected Nodes
getNodes :: TreeView -> ListStore (LNode DGNodeLab) -> IO [LNode DGNodeLab]
getNodes view list = do
  selector <- treeViewGetSelection view
  rows <- treeSelectionGetSelectedRows selector
  mapM (\ (row:[]) -> listStoreGetValue list row) rows

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore (LNode DGNodeLab) -> ListStore String
            -> IO()
updateNodes view listNodes listFinder = do
  nodes' <- getNodes view listNodes
  -- get list of theories
  let ths = map (dgn_theory . snd) nodes'
  if ths == [] then return ()
    else do
      -- get sublogic of joined theories
      sublogic <- case ths of
        []    -> error "this is not possible!"
        th:[] -> return $ sublogicOfTh th
        th:r  -> do
          -- join theories
          th' <- flatG_sentences th r
          return $ sublogicOfTh th'
      -- update finder list
      updateFinder listFinder sublogic

-- | Update the list of finder
updateFinder :: ListStore String -> G_sublogics -> IO ()
updateFinder list sublogic = do
  listStoreClear list
  mapM_ (listStoreAppend list) $ foldr (\ n l -> if elem n l then l else n:l) []
        $ map (\ (a,_) -> getPName a) $ getConsCheckers
        $ findComorphismPaths logicGraph sublogic
