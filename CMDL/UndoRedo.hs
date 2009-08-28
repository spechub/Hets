{- |
Module      : $Header$
Description : description of undo and redo functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.UnDoRedo contains the implementation of the undo and redo commads
-}

module CMDL.UndoRedo
       ( cUndo
       , cRedo
       ) where


import Data.List((++))

import System.IO(IO)

import Interfaces.History(redoOneStep, undoOneStep)
import Interfaces.Command(showCmd)
import Interfaces.DataTypes(IntHistory(undoList, redoList),
                            CmdHistory(command), IntState(i_hist))

import CMDL.DataTypesUtils(genMessage)
import CMDL.DataTypes(CMDL_State(intState))

-- | Undoes the last command entered
cUndo :: CMDL_State -> IO CMDL_State
cUndo = cdo True

-- | Redoes the last undo command
cRedo :: CMDL_State -> IO CMDL_State
cRedo = cdo False

cdo :: Bool -> CMDL_State -> IO CMDL_State
cdo isUndo state =
   let msg = (if isUndo then "un" else "re") ++ "do"
   in case (if isUndo then undoList else redoList) . i_hist $ intState state of
    [] -> return $ genMessage [] ("Nothing to " ++ msg) state
    action : _ ->
      do
       nwIntState <- (if isUndo then undoOneStep else redoOneStep)
         $ intState state
       return . genMessage [] ("Action '"++ showCmd (command action)
                               ++  "' is now " ++ msg ++ "ne")
              $ state { intState = nwIntState }
