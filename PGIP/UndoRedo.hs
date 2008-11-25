{- |
Module      : $Header$
Description : description of undo and redo functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.UnDoRedo contains the implementation of the undo and redo commads
-}

module PGIP.UndoRedo
       ( cUndo
       , cRedo
       ) where


import Interfaces.DataTypes
import Interfaces.History
import PGIP.DataTypes
import PGIP.DataTypesUtils
import System.IO
import Data.List

-- | Undoes the last command entered
cUndo :: CMDL_State -> IO CMDL_State
cUndo state =
  case undoList $ i_hist $ intState state of
   [] -> return $ genMessage [] "Nothing to undo" state
   action:_ -> return $ genMessage [] ("Action '"++(cmdName action)
                           ++ "' is now undone") $
                           state {
                            intState = undoOneStep $ intState state }

-- | Redoes the last undo command
cRedo :: CMDL_State -> IO CMDL_State
cRedo state =
   case redoList $ i_hist $ intState state of
    [] -> return $ genMessage [] "Nothing to redo" state
    action:_ -> return $ genMessage [] ("Action '"++(cmdName action)
                          ++  "' is now redone") $
                           state {
                             intState = redoOneStep $ intState state }
