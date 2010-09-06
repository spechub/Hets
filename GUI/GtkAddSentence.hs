{- |
Module      :  $Header$
Description :  Gtk GUI for adding a sentence
Copyright   :  (c) C. Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports existential types)

This module provides a GUI to add a sentence
-}

module GUI.GtkAddSentence where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.TextField as TextField
import GUI.GraphTypes

import Static.DevGraph

gtkAddSentence :: GInfo -> Int -> DGraph -> IO ()
gtkAddSentence _ n dg = postGUIAsync $ do
  xml <- getGladeXML TextField.get
  -- get objects
  window <- xmlGetWidget xml castToWindow "TextField"
  btnAbort <- xmlGetWidget xml castToButton "abort"
  btnAdd <- xmlGetWidget xml castToButton "add"
  entry <- xmlGetWidget xml castToEntry "entry"
  let lbl = labDG dg n
      name = getDGNodeName lbl
  windowSetTitle window $ "Add sentence to " ++ name
  onClicked btnAbort $ widgetDestroy window
  onClicked btnAdd $ do
    sen <- entryGetText entry
    putStrLn sen
  widgetShow window
