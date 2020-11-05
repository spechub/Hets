{- |
Module      :  ./GUI/GtkLinkTypeChoice.hs
Description :  Gtk GUI for the selection of linktypes
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the selection of linktypes.
-}

module GUI.GtkLinkTypeChoice
  (showLinkTypeChoice)
  where

import Graphics.UI.Gtk

import GUI.GtkUtils
import qualified GUI.Glade.LinkTypeChoice as LinkTypeChoice

import Static.DgUtils

import Control.Monad (filterM)

import Data.IORef
import qualified Data.HashMap.Lazy as Map

mapEdgeTypesToNames :: Map.HashMap String (DGEdgeType, DGEdgeType)
mapEdgeTypesToNames = Map.fromList $ map
  (\ e -> ("cb" ++ getDGEdgeTypeName e, (e, e { isInc = True })))
  (filter (not . isInc) listDGEdgeTypes)

-- | Displays the linktype selection window
showLinkTypeChoice :: IORef [String] -> ([DGEdgeType] -> IO ()) -> IO ()
showLinkTypeChoice ioRefDeselect updateFunction = postGUIAsync $ do
  builder <- getGTKBuilder LinkTypeChoice.get
  window <- builderGetObject builder castToWindow "linktypechoice"
  ok <- builderGetObject builder castToButton "btnOk"
  cancel <- builderGetObject builder castToButton "btnCancel"
  select <- builderGetObject builder castToButton "btnSelect"
  deselect <- builderGetObject builder castToButton "btnDeselect"
  invert <- builderGetObject builder castToButton "btnInvert"

  deselectEdgeTypes <- readIORef ioRefDeselect
  mapM_ (\ name -> do
          cb <- builderGetObject builder castToCheckButton name
          toggleButtonSetActive cb False
        ) deselectEdgeTypes

  let
    edgeMap = mapEdgeTypesToNames
    keys = Map.keys edgeMap
    setAllTo to = mapM_ (\ name -> do
                                cb <- builderGetObject builder castToCheckButton name
                                to' <- to cb
                                toggleButtonSetActive cb to'
                              ) keys

  onClicked select $ setAllTo (\ _ -> return True)
  onClicked deselect $ setAllTo (\ _ -> return False)
  onClicked invert $ setAllTo (\ cb -> do
                                selected <- toggleButtonGetActive cb
                                return $ not selected
                              )

  onClicked cancel $ widgetDestroy window

  onClicked ok $ do
    edgeTypeNames <- filterM (\ name -> do
                               cb <- builderGetObject builder castToCheckButton name
                               selected <- toggleButtonGetActive cb
                               return $ not selected
                             ) keys
    writeIORef ioRefDeselect edgeTypeNames
    let edgeTypes = foldl (\ eList (e, eI) -> e : eI : eList) []
                           $ map (flip (Map.findWithDefault
                                   (error "GtkLinkTypeChoice: lookup error!"))
                                   edgeMap
                                 ) edgeTypeNames
    forkIO_ $ updateFunction edgeTypes
    widgetDestroy window

  widgetShow window
