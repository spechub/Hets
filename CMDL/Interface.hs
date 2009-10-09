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

import System.Console.Haskeline

import System.IO (IO, hIsTerminalDevice, stdin)

import CMDL.Commands (getCommands)
import CMDL.DataTypes
import CMDL.DataTypesUtils (generatePrompter)
import CMDL.DgCommands (cUse)
import CMDL.Shell (checkCom, cmdlCompletionFn)
import CMDL.ProcessScript
import CMDL.Utils (stripComments)

import Interfaces.Command (Command(..), eqCmd, cmdNameStr)

import Common.Utils (trim)

import Data.List (find, isPrefixOf)

import Control.Concurrent.MVar
import Control.Monad (when)
import Control.Monad.Trans (MonadIO(..))

import Driver.Options (HetcatsOpts, InType(..), guess)

shellSettings :: MVar CmdlState -> Settings IO
shellSettings st =
  Settings {
      complete = cmdlComplete st
    , historyFile = Just "consoleHistory.tmp"
    , autoAddHistory = True
  }

-- We need an MVar here
-- because our CmdlState is not a Monad (and we use IO as Monad).
cmdlComplete :: MVar CmdlState -> CompletionFunc IO
cmdlComplete st (left, _) = do
  state <- liftIO $ readMVar st
  comps <- liftIO $ cmdlCompletionFn getCommands state $ reverse left
  let cmds = "prove-all" : map (cmdNameStr . cmdDescription) getCommands
      cmdcomps = filter (isPrefixOf (reverse left)) cmds
  return ("", map simpleCompletion $ comps ++ cmdcomps)

-- | Processes a list of input files
processInput :: HetcatsOpts -> [FilePath] -> CmdlState -> IO CmdlState
processInput opts ls state = case ls of
    []   -> return state
    l : ll -> (case guess l GuessIn of
               ProofCommand -> cmdlProcessScriptFile
               _ -> cUse) l state >>= processInput opts ll

shellLoop :: MVar CmdlState -> Bool -> InputT IO CmdlState
shellLoop st isTerminal =
  do
    state <- liftIO $ readMVar st
    minput <- getInputLine (if isTerminal then generatePrompter state else "")
    case minput of
      Nothing    -> return state
      Just input ->
        do
          let echo = trim $ stripComments input
          when (not isTerminal && not (null echo))
               (outputStrLn $ generatePrompter state ++ echo)
          (state', mc) <- liftIO $ cmdlProcessString "" 0 input state
          case mc of
            Nothing -> if any (input ==) ["exit", ":q"] -- additional exit cmds
                         then return state'
                         else do
                                outputStrLn $ "Unknown command: " ++ input
                                shellLoop st isTerminal
            Just ExitCmd -> return state'
            Just c -> do
                        newState <- liftIO $ printCmdResult state'
                        newState' <- liftIO $ case find
                                       (eqCmd c . cmdDescription) getCommands of
                                         Nothing -> return newState
                                         Just cm -> checkCom
                                              cm { cmdDescription = c } newState
                        liftIO $ swapMVar st newState'
                        shellLoop st isTerminal

-- | The function runs hets in a shell
cmdlRunShell :: HetcatsOpts -> [FilePath] -> IO CmdlState
cmdlRunShell opts files = do
  isTerminal <- hIsTerminalDevice stdin
  state <- processInput opts files (emptyCmdlState opts)
  st <- newMVar state
  runInputT (shellSettings st) $ shellLoop st isTerminal
