{- |
Module      :$Header$
Description : The definition of string processing interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.StringInterface describes the interface specific function
for string input
-}


module CMDL.StringInterface
        ( stringShellDescription
        , stringBackend
        , stringGetSingleChar
        , stringGetInput
        ) where

import System.Console.Shell(CommandStyle(OnlyCommands), ShellDescription(..),
                            initialShellDescription)
import System.Console.Shell.Backend(ShellBackend(..))
import System.IO(IO, stdout, putStrLn, hFlush)

import Control.Concurrent.MVar(MVar, newMVar, readMVar, swapMVar)

import CMDL.DataTypes(CmdlState)
import CMDL.Commands(shellacCommands, shellacEvalFunc)

-- | Creates the Backend for reading from files
stringBackend :: String -> ShellBackend (MVar String)
stringBackend input = ShBackend
  { initBackend = newMVar input
  , shutdownBackend = \_ -> return ()
  , outputString = \_ -> \_ -> return ()
  , flushOutput = \_ -> hFlush stdout
  , getSingleChar = stringGetSingleChar
  , getInput = stringGetInput
  , addHistory = \_ _ -> return ()
  , setWordBreakChars = \_ _ -> return ()
  , getWordBreakChars = \_ -> return
                      " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
  , onCancel = \_ -> putStrLn "canceled...\n"
  , setAttemptedCompletionFunction = \_ _ -> return ()
  , setDefaultCompletionFunction = \_ _ -> return ()
  , completeFilename = \_ _ -> return []
  , completeUsername = \_ _ -> return []
  , clearHistoryState = \_ -> return ()
  , getMaxHistoryEntries = \_ -> return 0
  , setMaxHistoryEntries = \_ _ -> return ()
  , readHistory = \_ _ -> return ()
  , writeHistory = \_ _ -> return ()
  }

-- | Used to get one char from a string
stringGetSingleChar :: MVar String -> String -> IO (Maybe Char)
stringGetSingleChar st _
 = do
    str <- readMVar st
    case str of
     []  -> return Nothing
     x:l -> do
             swapMVar st l
             return $ Just x


-- | Used to get a line from a file open for reading
stringGetInput :: MVar String -> String -> IO (Maybe String)
stringGetInput st _
 = do
    str <-readMVar st
    case lines str of
     []  -> return Nothing
     x:l -> do
             swapMVar st $ unlines l
             return $ Just x


stringShellDescription :: ShellDescription CmdlState
stringShellDescription =
 let wbc = "\t\n\r\v\\" in
      initialShellDescription
       { shellCommands      = shellacCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \_ -> return []
       , historyFile        = Nothing
       }
