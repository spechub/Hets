{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  A process interface for communication with other programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

Interface for communication with other processes
-}

module Interfaces.Process where

import Control.Monad (liftM)
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (MonadState (..))

import Data.Time.Clock
import Data.Time.Clock.POSIX

import qualified System.Process as SP
import System.Exit
import System.IO

import Common.IOS

-- * ReadState, controlled reading from a handle

type Time = NominalDiffTime

data IntelligentReadState = IRS { timeout :: Time      -- ^ total timeout
                                , started :: Time      -- ^ start timestamp
                                , updated :: Time      -- ^ last update stamp
                                , readtime :: Time     -- ^ stamp of last read
                                , hasread :: Bool      -- ^ got data
                                , waitForRead :: Bool
                                } deriving Show

initIRS :: Time -> Bool -> IO IntelligentReadState
initIRS t b = do{ ts <- getPOSIXTime; return $ IRS t ts ts 0 False b }

{- |
This class provides an interface to control the output retrieval from an
output handler (in the code of getOutput' you can see this control in action).
-}
class ReadState a where
    -- | For updating the ReadState, you may want to set new timestamps, etc.
    increment :: a      -- ^ the ReadState
              -> Bool   -- ^ a flag for "got data"
              -> IO a   -- ^ the updated readstate
    -- | A predicate to tell when to abort a read-try, usally when some
    -- timeout has passed
    abort :: a -> Bool

instance ReadState IntelligentReadState where
    increment irs@(IRS to st _ _ _ b) ngd =
        do{ ts <- getPOSIXTime
-- TODO: if-part also with irs-update
          ; return $ if ngd then (IRS to st ts ts ngd b) else irs{updated = ts}
          }
    abort (IRS to st lus slr gd b) =
        to <= lus - st || ((not b || gd) && let tr = lus - slr in tr > 0 && to / tr < 10)

getOutput :: (ReadState a) => Handle -> a -> IO String
getOutput hdl rs =
    do{ s <- getOutput' rs hdl ""
      ; return $ reverse s }

-- builds the string in the wrong order
-- tail-recursive function shouldn't make stack problems
getOutput' :: (ReadState a) => a -> Handle -> String -> IO String
getOutput' rs hdl s = 
    do{ b <- if abort rs then return Nothing -- timeout gone
             -- eventually error on eof so abort
             else catch (liftM Just $ hWaitForInput hdl 5) $ const $ return Nothing
      ; case b of Nothing -> return s
                  Just b' ->
                      do{ ns <- if b' then liftM (:s) $ hGetChar hdl else return s
                        ; nrs <- increment rs b'
                        ; getOutput' nrs hdl ns }
      }

-- | From given Time a ReadState is created and the output is fetched using
-- getOutput
getOutp :: Handle -> Time -> IO String
getOutp hdl t = initIRS t True >>= getOutput hdl


-- * A Command Interface using the intelligent read state

-- | This is just a type to hold the information returned by
--  System.Process.runInteractiveCommand
data CommandState = CS { inp :: Handle, outp :: Handle, err :: Handle,
                         pid :: SP.ProcessHandle }

-- | The IO State-Monad with state Maybe CommandState
type Command = IOS CommandState

-- | run communication program
runProg :: CommandState -- ^ initial comand state
        -> Command a    -- ^ command to be run
        -> IO CommandState -- ^ terminal command state
runProg cs cmd = fmap snd $ runIOS cmd cs

-- | run program with initialization
runProgInit :: String       -- ^ shell string to run the program
            -> Command a    -- ^ command to be run
            -> IO CommandState -- ^ terminal command state
runProgInit s cmd = start s >>= flip runProg cmd

-- | initialize the connection by running the given command string
start :: String -> IO CommandState
start cmd = do
  putStrLn $ "Running " ++ cmd ++ " ..."
  (i,o,e,p) <- SP.runInteractiveCommand $ cmd
  -- configure the handles 
  mapM_ (flip hSetBinaryMode False) [i, o, e]
  mapM_ (flip hSetBuffering NoBuffering) [o, e]
  hSetBuffering i LineBuffering
  -- clear all output from the output pipe (wait 300 milliseconds)
  getOutp o 0.3
  return $ CS i o e p

-- | Just read output from the connection waiting at most Time
readOutput :: Time -> Command String
readOutput t = 
    do{ s <- get
      ; liftIO $ getOutp (outp s) t }

-- | Just read error output from the connection waiting at most Time
readErr :: Time -> Command String
readErr t = 
    do{ s <- get
      ; liftIO $ getOutp (err s) t }

-- | Send some exit command if there is one to close the connection
close :: Maybe String -> Command ExitCode
close str = 
    do{ s <- get
      ; case str of Nothing -> return ()
                    _ -> liftIO $ hPutStrLn (inp s) "quit"
      ; e <- liftIO $ SP.waitForProcess $ pid s
      ; return e }

-- | Send some String and don't wait for response
send :: String -> Command ()
send str =
    do{ s <- get
      ; liftIO $ hPutStrLn (inp s) str }

-- | Send some String and wait Time for response
call :: Time   -- ^ Waits this time until abort call (Use float for seconds)
     -> String -- ^ Send this string over the connection
     -> Command String -- ^ Response
call t str =
    do{ s <- get
      -- first clear all output from the output pipe (wait 50 milliseconds)
      ; liftIO $ getOutp (outp s) 0.05
      ; liftIO $ hPutStrLn (inp s) str
      ; liftIO $ getOutp (outp s) t }

