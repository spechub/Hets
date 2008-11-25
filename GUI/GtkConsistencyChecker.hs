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

import Proofs.AbstractState (getConsCheckers, getPName)
import Logic.Grothendieck (findComorphismPaths)
import Comorphisms.LogicGraph(logicGraph)
import Static.DevGraph(DGraph, dgn_theory, labDG)
import Static.GTheory(sublogicOfTh)

import Monad (mapM_)
import Data.IORef

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> Int -> DGraph  -> IO ()
showConsistencyChecker _ descr dgraph  = postGUIAsync $ do
  xml                 <- getGladeXML ConsistencyChecker.get
  -- get objects
  window              <- xmlGetWidget xml castToWindow "ConsistencyChecker"
  btnShowTheory       <- xmlGetWidget xml castToButton "btnShowTheory"
  btnClose            <- xmlGetWidget xml castToButton "btnClose"
  btnSelection        <- xmlGetWidget xml castToButton "btnSelection"
  btnShowCASL         <- xmlGetWidget xml castToButton "btnShowCASL"
  btnShowTPTP         <- xmlGetWidget xml castToButton "btnShowTPTP"
  btnDisplay          <- xmlGetWidget xml castToButton "btnDisplay"
  btnDetails          <- xmlGetWidget xml castToButton "btnDetails"
  btnCheckConsistency <- xmlGetWidget xml castToButton "btnCheckConsistency"
  trvModel            <- xmlGetWidget xml castToTreeView "trvModel"
  trvFinder           <- xmlGetWidget xml castToTreeView "trvFinder"

  set window [windowTitle := "Consistency Checker"]
  setListData trvModel (\ a -> a) ["Test1", "Test2", "Test3", "Test4"]

  setModelListSelector trvModel
  setFinderListSelector trvFinder

  setListData trvFinder (\ n -> n)
                        $ foldr (\ n l -> if elem n l then l else n:l) []
                        $ map (\ (a,_) -> getPName a)
                        $ getConsCheckers $ findComorphismPaths logicGraph
                        $ sublogicOfTh $ dgn_theory $ labDG dgraph descr

  -- bindings
  onClicked btnClose $ widgetDestroy window
  onClicked btnShowTheory $ return ()
  onClicked btnSelection $ return ()
  onClicked btnShowCASL $ return ()
  onClicked btnShowTPTP $ return ()
  onClicked btnDisplay $ return ()
  onClicked btnDetails $ return ()
  onClicked btnCheckConsistency $ return ()

  widgetShow window

setFinderListSelector :: MV.TreeView -> IO ()
setFinderListSelector view = do
  selector <- MV.treeViewGetSelection view
  MV.treeSelectionSetMode selector MV.SelectionSingle

setModelListSelector :: MV.TreeView -> IO ()
setModelListSelector view = do
  selector <- MV.treeViewGetSelection view
  MV.treeSelectionSetMode selector MV.SelectionMultiple

  ioRefSelection <- newIORef ([] :: [MV.TreePath])
  MV.onCursorChanged view $ do
    s' <- MV.treeSelectionGetSelectedRows selector
    s <- readIORef ioRefSelection
    let newSelection = [ x | x <- s', notElem x s]
                    ++ [ x | x <- s, notElem x s']
    writeIORef ioRefSelection newSelection
    MV.treeSelectionUnselectAll selector
    mapM_ (\ path -> MV.treeSelectionSelectPath selector path) newSelection

  MV.treeSelectionSelectAll selector
