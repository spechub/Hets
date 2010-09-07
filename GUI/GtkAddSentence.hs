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
import Static.GTheory

import Logic.Logic
import Logic.Prover

import Common.AnnoState (emptyAnnos)
import Common.Doc
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Parsec
import Common.Result
import Common.Utils

import Control.Monad

import Text.ParserCombinators.Parsec

gtkAddSentence :: GInfo -> Int -> DGraph -> IO ()
gtkAddSentence gi n dg = postGUIAsync $ do
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
    abort <- anaSentence gi n dg lbl sen
    when abort $ widgetDestroy window
  widgetShow window

errorFeedback :: Bool -> String -> IO Bool
errorFeedback abort msg =
   errorDialogExt "Error" msg >> return abort

anaSentence :: GInfo -> Int -> DGraph -> DGNodeLab -> String -> IO Bool
anaSentence gi n dg lbl sen = case dgn_theory lbl of
  G_theory lid sign si sens _ -> case parse_basic_spec lid of
    Nothing -> errorFeedback True "missing basic spec parser"
    Just p -> case basic_analysis lid of
      Nothing -> errorFeedback True "missing basic analysis"
      Just f -> case runParser (p << eof) (emptyAnnos ()) "" $ trimLeft sen of
        Left err -> errorFeedback False $ show err
        Right bs -> let
          ps = plainSign sign
          Result ds res = f (bs, ps, emptyGlobalAnnos)
          in case res of
            Nothing -> errorFeedback False $ showRelDiags 1 ds
            Just (_, ExtSign sig2 _, sens2) ->
              if is_subsig lid sig2 ps then case sens2 of
                [ns] -> do
                  print $ print_named lid ns
                  addSentence gi n dg lbl
                    $ G_theory lid sign si (joinSens (toThSens sens2) sens)
                      startThId
                  return True
                [] -> errorFeedback False "no sentence recognized"
                _ -> errorFeedback False $ "multiple sentences recognized\n"
                     ++ show (vcat $ map (print_named lid) sens2)
              else errorFeedback False "signature must not change"

addSentence :: GInfo -> Int -> DGraph -> DGNodeLab -> G_theory -> IO ()
addSentence _gi _n _dg _lbl _th = return ()
