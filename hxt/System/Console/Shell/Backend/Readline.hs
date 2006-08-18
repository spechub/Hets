{-
 - 
 -  Copyright 2005-2006, Robert Dockins.
 -  
 -}

{- | This module implements a Shellac backend based on the GNU readline
     and GNU history modules.  For readline, we use the bindings
     from the standard library.  For history, we import directily using
     FFI.  This Shellac backend supports command completion, history buffer
     and all the line editing and character binding features of GNU readline.

     Beware that while the code for this Shellac binding is licensed under a BSD3
     license, GNU readline itself is licensed under the GPL.  This means that your
     project needs to be GPL compatible for this Shellac backend to be useful to you.
-}


module System.Console.Shell.Backend.Readline
( readlineBackend
) where

import System.IO            ( stdin, stdout, stderr, hFlush, hPutStr, hPutStrLn, hGetChar
                            , hSetBuffering, hGetBuffering
                            , BufferMode(..)
                            )
import Foreign.Ptr          ( Ptr )
import Foreign.C            ( CInt, CString, withCString )
import Foreign.C.Error      ( Errno, eOK, errnoToIOError )
import Foreign.Storable     ( peek )

import qualified Control.Exception as Ex
import qualified System.Console.Readline as RL

import System.Console.Shell.Backend 

readlineBackend :: ShellBackend String
readlineBackend = ShBackend
  { initBackend                      = return ""
  , outputString                     = \x -> readlineOutput x
  , flushOutput                      = \_ -> hFlush stdout
  , getInput                         = \_ -> RL.readline
  , getSingleChar                    = \_ -> readlineGetSingleChar
  , addHistory                       = \_ -> RL.addHistory
  , getWordBreakChars                = \_ -> RL.getBasicWordBreakCharacters
  , setWordBreakChars                = \_ -> RL.setBasicWordBreakCharacters
  , onCancel                         = \_ -> hPutStrLn stdout "canceled..."
  , setAttemptedCompletionFunction   = \_ -> readlineCompletionFunction
  , setDefaultCompletionFunction     = \_ -> RL.setCompletionEntryFunction
  , completeFilename                 = \_ -> RL.filenameCompletionFunction
  , completeUsername                 = \_ -> RL.filenameCompletionFunction
  , clearHistoryState                = \_ -> doClearHistoryState
  , setMaxHistoryEntries             = \_ -> doSetMaxHistoryEntries
  , getMaxHistoryEntries             = \_ -> doGetMaxHistoryEntries
  , readHistory                      = \_ -> doReadHistory
  , writeHistory                     = \_ -> doWriteHistory
  }


readlineCompletionFunction :: CompletionFunction -> IO ()
readlineCompletionFunction f = RL.setAttemptedCompletionFunction (Just complete)

 where complete word begin end = do
          buffer <- RL.getLineBuffer
          let before = take begin buffer
          let after  = drop end buffer

          f (before,word,after)


readlineGetSingleChar :: String -> IO (Maybe Char)
readlineGetSingleChar prompt = do
   hPutStr stdout prompt
   hFlush stdout
   Ex.bracket (hGetBuffering stdin) (hSetBuffering stdin) $ \_ -> do
      hSetBuffering stdin NoBuffering
      c <- hGetChar stdin
      hPutStrLn stdout ""
      return (Just c)

-- foreign import ccall "readline/history.h history_get_history_state" history_get_history_state :: IO (Ptr ())
-- foreign import ccall "readline/history.h history_set_history_state" history_set_history_state :: Ptr () -> IO ()
foreign import ccall "readline/history.h clear_history" clear_history :: IO ()
foreign import ccall "readline/history.h stifle_history" stifle_history :: CInt -> IO ()
foreign import ccall "readline/history.h unstifle_history" unstifle_history :: IO CInt
foreign import ccall "readline/history.h read_history" read_history :: CString -> IO Errno
foreign import ccall "readline/history.h write_history" write_history :: CString -> IO Errno
foreign import ccall "readline/history.h history_max_entries" history_max_entries :: Ptr CInt

doClearHistoryState :: IO ()
doClearHistoryState = clear_history

doSetMaxHistoryEntries :: Int -> IO ()
doSetMaxHistoryEntries m = stifle_history (fromIntegral m)

doGetMaxHistoryEntries :: IO Int
doGetMaxHistoryEntries = peek history_max_entries >>= return . fromIntegral

doReadHistory :: FilePath -> IO ()
doReadHistory path = do
  err <- withCString path read_history
  if err == eOK
     then return ()
     else ioError $ errnoToIOError 
              "System.Console.Shell.Backend.Readline.doReadHistory"
              err
              Nothing
              (Just path)

doWriteHistory :: FilePath -> IO ()
doWriteHistory path = do
  err <- withCString path write_history
  if err == eOK
     then return ()
     else ioError $ errnoToIOError
              "System.Console.Shell.Backend.Readline.doWriteHistory"
              err
              Nothing
              (Just path)

readlineOutput :: String -> BackendOutput -> IO ()
readlineOutput x (RegularOutput str)  = hPutStr stdout ("\n"++str++"\n")
readlineOutput x (InfoOutput str)     = hPutStr stdout ("\n"++str++"\n")
readlineOutput x (ErrorOutput str)    = hPutStr stderr ("\n"++str++"\n")
