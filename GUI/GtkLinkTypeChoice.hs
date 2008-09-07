{- |
Module      :  $Header$
Description :  Gtk GUI for the selection of linktypes
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the selection of linktypes.
-}

module GUI.GtkLinkTypeChoice
  (showLinkTypeChoice)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import GUI.Glade.LinkTypeChoice

import Monad(foldM)

-- | Displays the linktype selection window
showLinkTypeChoice :: [String] -> ([String] -> IO ()) -> IO ()
showLinkTypeChoice linkTypes updateFunction = postGUIAsync $ do
  xml <- getGladeXML $ getLinkTypeChoice
  window   <- xmlGetWidget xml castToWindow "linktypechoice"
  ok       <- xmlGetWidget xml castToButton "b_ok"
  cancel   <- xmlGetWidget xml castToButton "b_cancel"

  onClicked cancel $ widgetDestroy window

  onClicked ok $ do
    checkButtons <- mapM (\ name -> do
                            cb <- xmlGetWidget xml castToCheckButton $
                                               "cb_" ++ name
                            return (name, cb)) linkTypes
    linkTypes' <- foldM (\ selected (name, cb) -> do
                           selection <- toggleButtonGetActive cb
                           case selection of
                             True -> return $ name:selected
                             False -> return selected) [] checkButtons
    updateFunction linkTypes'
    widgetDestroy window

  widgetShow window
