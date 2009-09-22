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

import Driver.Options (HetcatsOpts)

-- | Creates an empty CMDL_State
emptyCMDL_State :: HetcatsOpts -> CMDL_State
emptyCMDL_State opts = CMDL_State
  { intState = IntState
      { i_state = Nothing
      , i_hist = IntHistory
          { undoList = []
          , redoList = [] }
      , filename = [] }
  , prompter = CMDL_PrompterState
      { fileLoaded = ""
      , prompterHead = "> " }
  , output = CMDL_Message
      { errorMsg = []
      , outputMsg = []
      , warningMsg = [] }
  , openComment = False
  , connections = []
  , hetsOpts = opts }

-- | The function runs hets in a shell
cmdlRunShell :: HetcatsOpts -> [FilePath] ->IO CMDL_State
cmdlRunShell opts files =
      recursiveApplyUse files (emptyCMDL_State opts)
      >>= runShell stdShellDescription
                { defaultCompletions = Just (cmdlCompletionFn getCommands) }
#ifdef EDITLINE
              editlineBackend
#else
              haskelineBackend
#endif

-- | The function processes the file of instructions
cmdlProcessFile :: HetcatsOpts -> FilePath -> IO CMDL_State
cmdlProcessFile opts flnm = let st = emptyCMDL_State opts in
    runShell fileShellDescription (fileBackend flnm) st
    `catch` const (return st)

-- | The function processes a string of instructions starting from a given
-- state
cmdlProcessString :: String -> CMDL_State -> IO CMDL_State
cmdlProcessString input st =
    runShell stringShellDescription (stringBackend input) st
    `catch` const (return st)
