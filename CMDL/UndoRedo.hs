{- |
Module      : ./CMDL/UndoRedo.hs
Description : description of undo and redo functions
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.UnDoRedo contains the implementation of the undo and redo commads
-}


module CMDL.UndoRedo
       ( cUndo
       , cRedo
       ) where


import Interfaces.History (redoOneStep, undoOneStep)
import Interfaces.Command (showCmd)
import Interfaces.DataTypes

import CMDL.DataTypesUtils (genMessage)
import CMDL.DataTypes (CmdlState (intState))

-- | Undoes the last command entered
cUndo :: CmdlState -> IO CmdlState
cUndo = cdo True

-- | Redoes the last undo command
cRedo :: CmdlState -> IO CmdlState
cRedo = cdo False

cdo :: Bool -> CmdlState -> IO CmdlState
cdo isUndo state =
   let msg = (if isUndo then "un" else "re") ++ "do"
   in case (if isUndo then undoList else redoList) . i_hist $ intState state of
    [] -> return $ genMessage [] ("Nothing to " ++ msg) state
    action : _ ->
      do
       nwIntState <- (if isUndo then undoOneStep else redoOneStep)
         $ intState state
       return . genMessage [] ("Action '" ++ showCmd (command action)
                               ++ "' is now " ++ msg ++ "ne")
              $ state { intState = nwIntState }
