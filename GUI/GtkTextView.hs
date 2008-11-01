{- |
Module      :  $Header$
Description :  Gtk GUI for the selection of linktypes
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Provides a window with a single textview.
-}

module GUI.GtkTextView
  (showTextView)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.TextView as TextView

-- | Displays the linktype selection window
showTextView :: String -> IO ()
showTextView title = postGUIAsync $ do
  xml    <- getGladeXML TextView.get
  window <- xmlGetWidget xml castToWindow "TextView"
  close  <- xmlGetWidget xml castToButton "btnClose"
  label  <- xmlGetWidget xml castToLabel "labTitle"
  list   <- xmlGetWidget xml castToTextView "tvList"

  -- set headline
  labelSetLabel label title

  -- get buffer of textview
  buffer <- textViewGetBuffer list

  {- get tag table
     tag are descriping the formatation of text, like color, font, etc.
     all tags need to be stored in the tagtable of the buffer.
  -}
  tagTable <- textBufferGetTagTable buffer
  
  -- create a tag for red text
  coloredTag <- textTagNew Nothing
  set coloredTag [ textTagForeground := "red" ]
  -- add tag to table
  textTagTableAdd tagTable coloredTag
  
  -- create a tag for red backgrounded text
  backgroundTag <- textTagNew Nothing
  set backgroundTag [ textTagBackground := "red" ]
  -- add tag to table
  textTagTableAdd tagTable backgroundTag

  -- insert text with tabs
  textBufferInsertAtCursor buffer $
    "This is a test with tabs and colors\n" ++
    "\tthis should be colored\n" ++
    "\tthis has a backgroundcolor\n" ++
    "\tthis is normal\n"

  -- get iterator of second line start (after tab) and end
  -- linecount is starting with 0
  itColoredStart <- textBufferGetIterAtLineOffset buffer 1 1
  itColoredEnd <- textBufferGetIterAtLineOffset buffer 1 1
  textIterForwardToLineEnd itColoredEnd
  -- apply a tag for the interval
  textBufferApplyTag buffer coloredTag itColoredStart itColoredEnd

  -- get iterator of third line start (after tab) and end
  itBackgroundStart <- textBufferGetIterAtLineOffset buffer 2 1
  itBackgroundEnd <- textBufferGetIterAtLineOffset buffer 2 1
  textIterForwardToLineEnd itBackgroundEnd
  -- apply a tag for the interval
  textBufferApplyTag buffer backgroundTag itBackgroundStart itBackgroundEnd

  -- add function for closebutton
  onClicked close $ widgetDestroy window

  widgetShow window
