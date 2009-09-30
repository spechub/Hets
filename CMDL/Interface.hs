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
import CMDL.DataTypes(CmdlMessage(..), CmdlPrompterState(..), CmdlState(..))
import CMDL.Shell(cmdlCompletionFn)

import CMDL.FileInterface(fileBackend, fileShellDescription)
import CMDL.StdInterface(recursiveApplyUse, stdShellDescription)
import CMDL.StringInterface(stringBackend, stringShellDescription)

import Interfaces.DataTypes

import Driver.Options (HetcatsOpts, InType(..), guess)

-- | Creates an empty CmdlState
emptyCmdlState :: HetcatsOpts -> CmdlState
emptyCmdlState opts = CmdlState
  { intState = IntState
      { i_state = Nothing
      , i_hist = IntHistory
          { undoList = []
          , redoList = [] }
      , filename = [] }
  , prompter = CmdlPrompterState
      { fileLoaded = ""
      , prompterHead = "> " }
  , output = CmdlMessage
      { errorMsg = []
      , outputMsg = []
      , warningMsg = [] }
  , openComment = False
  , connections = []
  , hetsOpts = opts }

-- | The function runs hets in a shell
cmdlRunShell :: HetcatsOpts -> [FilePath] -> IO CmdlState
cmdlRunShell opts files = do
  let isHPF fls = length fls == 1 && case guess (head fls) GuessIn of
                                       ProofCommand -> True
                                       _            -> False
  state <- if isHPF files
             then cmdlProcessFile opts $ head files
             else recursiveApplyUse files (emptyCmdlState opts)
  shellDsc <- stdShellDescription
  runShell shellDsc { defaultCompletions = Just (cmdlCompletionFn getCommands) }
#ifdef EDITLINE
                  editlineBackend
#else
                  haskelineBackend
#endif
                  state

-- | The function processes the file of instructions
cmdlProcessFile :: HetcatsOpts -> FilePath -> IO CmdlState
cmdlProcessFile opts flnm = let st = emptyCmdlState opts in
    runShell fileShellDescription (fileBackend flnm) st

-- | The function processes a string of instructions starting from a given
-- state
cmdlProcessString :: String -> CmdlState -> IO CmdlState
cmdlProcessString input st =
    runShell stringShellDescription (stringBackend input) st
    `catch` const (return st)
