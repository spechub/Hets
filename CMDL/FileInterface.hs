{- |
Module      :$Header$
Description : The definition of file processing interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.FileInterface describes the interface specific function
for file input
-}


module CMDL.FileInterface
        ( fileShellDescription
        , fileBackend
        , fileGetSingleChar
        , fileGetInput
        ) where

import System.Console.Shell(CommandStyle(OnlyCommands), ShellDescription(..),
                            initialShellDescription)
import System.Console.Shell.Backend(ShellBackend(..))
import System.IO

import Control.Monad(when)

import CMDL.Commands(shellacCommands, shellacEvalFunc)
import CMDL.DataTypes(CMDL_State)
import CMDL.StdInterface(basicOutput)
import CMDL.Utils(stripComments)

import Common.Utils(trim)

import qualified Control.Exception as Ex

-- | Creates the Backend for reading from files
fileBackend :: String -> ShellBackend Handle
fileBackend filename = ShBackend
  { initBackend = openFile filename ReadMode
  , shutdownBackend = hClose
  , outputString = const basicOutput
  , flushOutput = \_ -> hFlush stdout
  , getSingleChar = fileGetSingleChar
  , getInput = fileGetInput
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

-- | Used to get one char from a file open for reading
fileGetSingleChar :: Handle -> String -> IO (Maybe Char)
fileGetSingleChar file _
 = Ex.bracket (hGetBuffering file) (hSetBuffering file) $
         \_ -> do
                hSetBuffering file NoBuffering
                c <- hGetChar file
                putStrLn []
                return (Just c)

-- | Used to get a line from a file open for reading
fileGetInput :: Handle -> String -> IO (Maybe String)
fileGetInput file _ = do
   x <- hGetLine file
   when (trim (stripComments x) /= "") (putStrLn $ "> " ++ x)
   return (Just x)


fileShellDescription :: ShellDescription CMDL_State
fileShellDescription =
 let wbc = "\t\n\r\v\\" in
      initialShellDescription
       { shellCommands      = shellacCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \_ -> return []
       , historyFile        = Nothing
       }
