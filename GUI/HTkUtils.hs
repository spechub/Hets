{-
Module      :  $Header$
Copyright   :  (c)  Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

   Utilities on top of HTk
-}

module GUI.HTkUtils where

import HTk
import Core
import ScrollBox
import MarkupText 

import TextDisplay

import System.Posix.IO

-- | create a window with title and list of options, return selected option
listBox :: String -> [String] -> IO (Maybe Int)
listBox title entries =
  do
    main <- createToplevel [text title]
    lb  <- newListBox main [value entries, bg "white", size (100, 50)] ::
             IO (ListBox String)
    pack lb [Side AtLeft, 
                 Expand On, Fill Both]
    scb <- newScrollBar main []
    pack scb [Side AtRight, Fill Y]
    lb # scrollbar Vertical scb
    (press, _) <- bindSimple lb (ButtonPress (Just 1))
    sync press
    sel <- getSelection lb
    destroy main
    return (case sel of
       Just [i] -> Just i
       _ -> Nothing)


---
-- Display some (longish) text in an uneditable, scrollable editor.
-- Returns immediately-- the display is forked off to separate thread.
-- @param title   - the title of the window
-- @param filename  - the filename for saving the text
-- @param txt     - the text to be displayed
-- @param conf    - configuration options for the text editor
-- @param unpost  - action to be executed when the window is closed
-- @return result - the window in which the text is displayed
createTextSaveDisplayExt :: String-> String -> String-> [Config Editor]-> IO()-> IO (Toplevel,
								       Editor)
createTextSaveDisplayExt title filename txt conf unpost =
  do win <- createToplevel [text title]
     b   <- newFrame win  [relief Groove, borderwidth (cm 0.05)]    
     t   <- newLabel b [text title, HTk.font (Helvetica, Roman, 18::Int)]
     q   <- newButton b [text "Close", width 12]
     s   <- newButton b [text "Save", width 12]
     (sb, ed) <- newScrollBox b (\p-> newEditor p (state Normal:conf)) []
     pack b [Side AtTop, Fill X, Expand On]
     pack t [Side AtTop, Expand Off, PadY 10]
     pack sb [Side AtTop, Expand On]
     pack ed [Side AtTop, Expand On, Fill X]
     pack q [Side AtRight, PadX 5, PadY 5] 		 
     pack s [Side AtLeft, PadX 5, PadY 5] 		 

     ed # value txt
     ed # state Disabled

     quit <- clicked q
     save <- clicked s
     spawnEvent (forever (quit >>> do destroy win; unpost
                           +>
                         save >>> do writeFile filename txt; createTextDisplay "" ("Wrote "++filename) [size(30,10)]))
     return (win, ed)

---
-- Display some (longish) text in an uneditable, scrollable editor.
-- Simplified version of createTextSaveDisplayExt
-- @param title   - the title of the window
-- @param filename  - the filename for saving the text
-- @param txt     - the text to be displayed
-- @param conf    - configuration options for the text editor
createTextSaveDisplay :: String-> String -> String-> [Config Editor]-> IO()
createTextSaveDisplay t f txt conf = do createTextSaveDisplayExt t f txt conf done; done
