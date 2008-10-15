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
import qualified GUI.Glade.LinkTypeChoice as LinkTypeChoice

import Monad(foldM)

-- | Displays the linktype selection window
showLinkTypeChoice :: [String] -> ([String] -> IO ()) -> IO ()
showLinkTypeChoice linkTypes updateFunction = postGUIAsync $ do
  xml      <- getGladeXML LinkTypeChoice.get
  window   <- xmlGetWidget xml castToWindow "linktypechoice"
  ok       <- xmlGetWidget xml castToButton "b_ok"
  cancel   <- xmlGetWidget xml castToButton "b_cancel"
  select   <- xmlGetWidget xml castToButton "b_select"
  deselect <- xmlGetWidget xml castToButton "b_deselect"
  invert   <- xmlGetWidget xml castToButton "b_invert"

  onClicked select $ mapM_ (\ name -> do
                             cb <- xmlGetWidget xml castToCheckButton $
                                               "cb_" ++ name
                             toggleButtonSetActive cb True
                           ) linkTypes

  onClicked deselect $ mapM_ (\ name -> do
                             cb <- xmlGetWidget xml castToCheckButton $
                                               "cb_" ++ name
                             toggleButtonSetActive cb False
                           ) linkTypes

  onClicked invert $ mapM_ (\ name -> do
                             cb <- xmlGetWidget xml castToCheckButton $
                                               "cb_" ++ name
                             selected <- toggleButtonGetActive cb
                             toggleButtonSetActive cb $ not selected
                           ) linkTypes

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
