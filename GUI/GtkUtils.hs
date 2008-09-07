{- |
Module      :  $Header$
Description :  Access to the .glade files stored as strings inside the binary
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

This module provides the ability to store xml stings in a temporary file to load
it with gtk2hs. This is needed, because gtk2hs needs glade files for input, but
we want to distribute them within the binary.
-}

module GUI.GtkUtils
  (getGladeXML, startMainLoop, stopMainLoop)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import Control.Concurrent

import System.Directory (removeFile, getTemporaryDirectory)
import System.IO (hFlush, hClose, hPutStr, openTempFile)

-- | Returns a GladeXML Object of a xmlstring.
getGladeXML :: (String, String) -> IO GladeXML
getGladeXML (name, xmlstr) = do
  temp <- getTemporaryDirectory
  (filename, handle) <- openTempFile temp name
  hPutStr handle xmlstr
  hFlush handle
  mxml <- xmlNew filename
  hClose handle
  removeFile filename
  case mxml of
    Just xml -> return xml
    Nothing -> error "GtkUtils: Can't load xml string."

-- | Starts the gtk main event loop in a thread
startMainLoop :: IO ()
startMainLoop = do
  forkIO $ do
    unsafeInitGUIForThreadedRTS
    mainGUI
  return ()

stopMainLoop :: IO ()
stopMainLoop = postGUISync $ do
  mainQuit