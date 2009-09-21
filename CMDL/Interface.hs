{-# LANGUAGE CPP #-}
{- |
Module      : $Header$
Description : The definition of CMDL interface for
              standard input and file input
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.Interface describes the interface specific function
for standard input and file input
-}

module CMDL.Interface where


import System.Console.Shell(ShellDescription(defaultCompletions), runShell)
#ifdef EDITLINE
import System.Console.Shell.Backend.Editline
#else
import System.Console.Shell.Backend.Haskeline
#endif
import System.IO(IO)

import CMDL.Commands(getCommands)
import CMDL.DataTypes(CMDL_Message(..), CMDL_PrompterState(..), CMDL_State(..))
import CMDL.Shell(cmdlCompletionFn)

import CMDL.FileInterface(fileBackend, fileShellDescription)
import CMDL.StdInterface(recursiveApplyUse, stdShellDescription)
import CMDL.StringInterface(stringBackend, stringShellDescription)

import Interfaces.DataTypes

-- | Creates an empty CMDL_State
emptyCMDL_State ::  CMDL_State
emptyCMDL_State =
   CMDL_State {
      intState = IntState {
                  i_state = Nothing,
                  i_hist = IntHistory {
                              undoList = [],
                              redoList = []},
                  filename = []

                        },
      prompter = CMDL_PrompterState {
                    fileLoaded = [],
                    prompterHead = "> " },
      output = CMDL_Message {
                 errorMsg   = [],
                 outputMsg  = [],
                 warningMsg = []
                  },
      openComment = False,
      connections = []
     }


-- | The function runs hets in a shell
cmdlRunShell :: [String] ->IO CMDL_State
cmdlRunShell files
   = do
      state <- recursiveApplyUse  files emptyCMDL_State
      runShell stdShellDescription
                {defaultCompletions= Just (cmdlCompletionFn getCommands) }
#ifdef EDITLINE
              editlineBackend
#else
              haskelineBackend
#endif
              state

-- | The function processes the file of instructions
cmdlProcessFile :: String -> IO CMDL_State
cmdlProcessFile flnm =
        runShell fileShellDescription (fileBackend flnm) emptyCMDL_State `catch`
        (\_ -> return emptyCMDL_State )

-- | The function processes a string of instructions starting from a given
-- state
cmdlProcessString :: String -> CMDL_State -> IO CMDL_State
cmdlProcessString input st =
       runShell stringShellDescription (stringBackend input) st `catch`
       (\_ -> return st )
