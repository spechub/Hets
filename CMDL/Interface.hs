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

import System.Console.Shell(CommandStyle(OnlyCommands), ShellDescription(..),
                            runShell, initialShellDescription)
import System.Console.Shell.Backend(ShellBackend(..))
import System.Console.Shell.Backend.Haskeline

import System.IO(IO, hIsTerminalDevice, stdin)

import CMDL.Commands(getCommands, shellacCommands, shellacEvalFunc)
import CMDL.DataTypes
import CMDL.DataTypesUtils(generatePrompter)
import CMDL.DgCommands(cUse)
import CMDL.Shell(cmdlCompletionFn)
import CMDL.Utils(stripComments)
import CMDL.ProcessScript

import Common.Utils(trim)
import Driver.Options (HetcatsOpts, InType(..), guess)

stdShellDescription :: ShellDescription CmdlState
stdShellDescription =
 let wbc = "\n\r\v\\"
  in initialShellDescription
          { shellCommands      = shellacCommands
          , commandStyle       = OnlyCommands
          , evaluateFunc       = shellacEvalFunc
          , wordBreakChars     = wbc
          , prompt             = return . generatePrompter
          , historyFile        = Just "consoleHistory.tmp"
          }

-- | Processes a list of input files
processInput :: HetcatsOpts -> [FilePath] -> CmdlState -> IO CmdlState
processInput opts ls state = case ls of
    []   -> return state
    l : ll -> (case guess l GuessIn of
               ProofCommand -> cmdlProcessScriptFile
               _ -> cUse) l state >>= processInput opts ll

-- | The function runs hets in a shell
cmdlRunShell :: HetcatsOpts -> [FilePath] -> IO CmdlState
cmdlRunShell opts files = do
  isTerm <- hIsTerminalDevice stdin
  state <- processInput opts files (emptyCmdlState opts)
  let backend = haskelineBackend
      backendEcho = backend
        { getInput = \ h s -> do
            res <- getInput backend h s
            case res of
              Just str -> putStrLn $ trim (stripComments str)
              Nothing -> return ()
            return res
        }
  runShell stdShellDescription
             { defaultCompletions = Just (cmdlCompletionFn getCommands) }
             (if isTerm then backend else backendEcho) state
