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

import GUI.GtkUtils
import GUI.Glade.ConsistencyChecker
import GUI.GraphTypes

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> IO ()
showConsistencyChecker _ = postGUIAsync $ do
  xml                 <- getGladeXML $ getConsistencyChecker

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
