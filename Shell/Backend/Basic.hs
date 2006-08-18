{-
 - 
 -  Copyright 2005-2006, Robert Dockins.
 -  
 -}


{- | This module implements a simple Shellac backend that uses only
     the primitaves from "System.IO".  It provides no history or
     command completion capabilities.  You get whatever line editing
     capabilities 'hGetLine' has and that's it.
-}

module Shell.Backend.Basic
( basicBackend
) where

import System.IO   ( stdout, stderr, stdin, hFlush, hPutStr, hPutStrLn
	           , hGetLine, hGetChar, hGetBuffering, hSetBuffering
                   , BufferMode(..)
                   )
import qualified Control.Exception as Ex

import Shell.Backend

basicBackend :: ShellBackend ()
basicBackend = ShBackend
  { initBackend                      = return ()
  , outputString                     = \_ -> basicOutput 
  , flushOutput                      = \_ -> hFlush stdout
  , getSingleChar                    = \_ -> basicGetSingleChar
  , getInput                         = \_ -> basicGetInput
  , addHistory                       = \_ _ -> return ()
  , setWordBreakChars                = \_ _ -> return ()
  , getWordBreakChars                = \_ -> return " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
  , onCancel                         = \_ -> hPutStrLn stdout "cancled...\n"
  , setAttemptedCompletionFunction   = \_ _ -> return ()
  , setDefaultCompletionFunction     = \_ _ -> return ()
  , completeFilename                 = \_ _ -> return []
  , completeUsername                 = \_ _ -> return []
  , clearHistoryState                = \_ -> return ()
  , getMaxHistoryEntries             = \_ -> return 0
  , setMaxHistoryEntries             = \_ _ -> return ()
  , readHistory                      = \_ _ -> return ()
  , writeHistory                     = \_ _ -> return ()
  }

basicGetSingleChar :: String -> IO (Maybe Char)
basicGetSingleChar prompt = do
   hPutStr stdout prompt
   hFlush stdout
   Ex.bracket (hGetBuffering stdin) (hSetBuffering stdin) $ \_ -> do
      hSetBuffering stdin NoBuffering
      c <- hGetChar stdin
      hPutStrLn stdout ""
      return (Just c)

basicGetInput :: String -> IO (Maybe String)
basicGetInput prompt = do
   hPutStr stdout prompt
   hFlush stdout
   x <- hGetLine stdin
   return (Just x)

basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = hPutStr stdout out
basicOutput (InfoOutput out)    = hPutStr stdout out
basicOutput (ErrorOutput out)   = hPutStr stderr out
