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

import Static.DevGraph

import Control.Monad(filterM)

import Data.IORef
import qualified Data.Map as Map

mapEdgeTypesToNames :: Map.Map String (DGEdgeType, DGEdgeType)
mapEdgeTypesToNames = Map.fromList $ map
  (\ e -> ("cb" ++ getDGEdgeTypeName e, (e, e { isInc = True })))
  (filter (not . isInc) listDGEdgeTypes)

-- | Displays the linktype selection window
showLinkTypeChoice :: IORef [String] -> ([DGEdgeType] -> IO ()) -> IO ()
showLinkTypeChoice ioRefDeselect updateFunction = postGUIAsync $ do
  xml      <- getGladeXML LinkTypeChoice.get
  window   <- xmlGetWidget xml castToWindow "linktypechoice"
  ok       <- xmlGetWidget xml castToButton "btnOk"
  cancel   <- xmlGetWidget xml castToButton "btnCancel"
  select   <- xmlGetWidget xml castToButton "btnSelect"
  deselect <- xmlGetWidget xml castToButton "btnDeselect"
  invert   <- xmlGetWidget xml castToButton "btnInvert"

  deselectEdgeTypes <- readIORef ioRefDeselect
  mapM_ (\ name -> do
          cb <- xmlGetWidget xml castToCheckButton name
          toggleButtonSetActive cb False
        ) deselectEdgeTypes

  let
    edgeMap = mapEdgeTypesToNames
    keys = Map.keys edgeMap
    setAllTo = (\ to -> mapM_ (\ name -> do
                                cb <- xmlGetWidget xml castToCheckButton name
                                to' <- to cb
                                toggleButtonSetActive cb to'
                              ) keys
               )

  onClicked select $ setAllTo (\ _ -> return True)
  onClicked deselect $ setAllTo (\ _ -> return False)
  onClicked invert $ setAllTo (\ cb -> do
                                selected <- toggleButtonGetActive cb
                                return $ not selected
                              )

  onClicked cancel $ widgetDestroy window

  onClicked ok $ do
    edgeTypeNames <- filterM (\ name -> do
                               cb <- xmlGetWidget xml castToCheckButton name
                               selected <- toggleButtonGetActive cb
                               return $ not selected
                             ) keys
    writeIORef ioRefDeselect edgeTypeNames
    let edgeTypes =  foldl (\ eList (e, eI) -> e:eI:eList) []
                           $ map (flip (Map.findWithDefault
                                   (error "GtkLinkTypeChoice: lookup error!"))
                                   edgeMap
                                 ) edgeTypeNames
    forkIO_ $ updateFunction edgeTypes
    widgetDestroy window

  widgetShow window
