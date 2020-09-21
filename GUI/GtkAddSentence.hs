{- |
Module      :  ./GUI/GtkAddSentence.hs
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

import GUI.GtkUtils
import qualified GUI.Glade.TextField as TextField
import GUI.GraphTypes
import GUI.GraphLogic

import Interfaces.Utils

import Static.DevGraph
import Static.GTheory
import Static.FromXmlUtils (BasicExtResponse (..), extendByBasicSpec)

import Common.GlobalAnnotations

import Control.Monad
import Data.IORef

gtkAddSentence :: GInfo -> Int -> DGraph -> IO ()
gtkAddSentence gi n dg = postGUIAsync $ do
  builder <- getGTKBuilder TextField.get
  -- get objects
  window <- builderGetObject builder castToWindow "TextField"
  btnAbort <- builderGetObject builder castToButton "abort"
  btnAdd <- builderGetObject builder castToButton "add"
  entry <- builderGetObject builder castToEntry "entry"
  let lbl = labDG dg n
      name = getDGNodeName lbl
  windowSetTitle window $ "Add sentence to " ++ name
  onClicked btnAbort $ widgetDestroy window
  onClicked btnAdd $ do
    sen <- entryGetText entry
    abort <- anaSentence gi (globalAnnos dg) n lbl sen
    when abort $ widgetDestroy window
  widgetShow window

errorFeedback :: Bool -> String -> IO Bool
errorFeedback abort msg =
   errorDialog "Error" msg >> return abort

anaSentence :: GInfo -> GlobalAnnos -> Int -> DGNodeLab -> String -> IO Bool
anaSentence gi ga n lbl sen = case extendByBasicSpec ga sen $ dgn_theory lbl of
  (Success gTh num _ sameSig, str)
    | not sameSig -> errorFeedback False $ "signature must not change\n" ++ str
    | num < 1 -> errorFeedback False "no sentence recognized"
    | num > 1 -> errorFeedback False $ "multiple sentences recognized\n" ++ str
    | otherwise -> do
         addSentence gi n lbl gTh
         return True
  (Failure b, str) -> errorFeedback b str

addSentence :: GInfo -> Int -> DGNodeLab -> G_theory -> IO ()
addSentence gi n lbl th = do
      let ln = libName gi
          iSt = intState gi
      ost <- readIORef iSt
      let (ost', hist) = updateNodeProof ln ost (n, lbl) th
      writeIORef iSt ost'
      runAndLock gi $ updateGraph gi hist
