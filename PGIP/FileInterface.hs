{- |
Module      :$Header$
Description : The definition of file processing interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.FileInterface describes the interface specific function
for file input
-}


module PGIP.FileInterface
        ( fileShellDescription
        , fileBackend
        , fileGetSingleChar
        , fileGetInput
        ) where


import System.Console.Shell
import System.Console.Shell.Backend
import System.IO

import PGIP.DataTypes
import PGIP.Commands
import PGIP.StdInterface

import qualified Control.Exception as Ex


-- | Creates the Backend for reading from files
fileBackend :: String -> ShellBackend Handle
fileBackend filename = ShBackend
  { initBackend = openFile filename ReadMode
  , shutdownBackend = hClose
  , outputString = \_ -> basicOutput
  , flushOutput = \_ -> hFlush stdout
  , getSingleChar = fileGetSingleChar
  , getInput = fileGetInput
  , addHistory = \_ _ -> return ()
  , setWordBreakChars = \_ _ -> return ()
  , getWordBreakChars = \_ -> return
                      " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
  , onCancel = \_ -> hPutStrLn stdout "canceled...\n"
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
 = do
    Ex.bracket (hGetBuffering file) (hSetBuffering file) $
         \_ -> do
                hSetBuffering file NoBuffering
                c <- hGetChar file
                hPutStrLn stdout []
                return (Just c)

-- | Used to get a line from a file open for reading
fileGetInput :: Handle -> String -> IO (Maybe String)
fileGetInput file _ = do
   x <- hGetLine file
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
