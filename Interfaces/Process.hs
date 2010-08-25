{- |
Module      :  $Header$
Description :  A process interface for communication with other programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

Interface for communication with other processes
-}

module Interfaces.Process where

import Control.Monad (liftM, when)
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (MonadState (..))

import Data.Time
import Data.Maybe

import qualified System.Process as SP
import System.Exit
import System.IO

import Common.IOS

-- ----------------------------------------------------------------------
-- * ReadState, controlled reading from a handle
-- ----------------------------------------------------------------------

type DTime = NominalDiffTime
type Time = UTCTime

data IntelligentReadState = IRS { timeout :: DTime     -- ^ total timeout
                                , started :: Time      -- ^ start timestamp
                                , updated :: Time      -- ^ last update stamp
                                , readtime :: Time     -- ^ stamp of last read
                                , hasread :: Bool      -- ^ got data
                                , waitForRead :: Bool  -- ^  
                                , waittimeInp :: Int   -- ^ same as waitForInp
                                } deriving Show

data TimeConfig = TimeConfig { waitForInp :: Int
                             -- ^ How many milliseconds waiting for next data
                             , startTimeout :: DTime
                             -- ^ Give the application some time to come up
                             , cleanTimeout :: DTime
                             -- ^ 
                             } deriving Show

defaultConfig :: TimeConfig
defaultConfig = TimeConfig { waitForInp = 1
                           , startTimeout = 0.7
                           , cleanTimeout = 0.001 }

zeroTime :: Time
zeroTime = UTCTime { utctDay = ModifiedJulianDay { toModifiedJulianDay = 0 }
                   , utctDayTime = 0 } -- 17.11.1858 00:00:00

initIRS :: Int -> DTime -> Bool -> IO IntelligentReadState
initIRS w t b = do
  ts <- getCurrentTime
  return $ IRS t ts ts zeroTime False b w

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
    -- | Wait-time for new input
    waitInp :: a   -- ^ the ReadState
            -> Int -- ^ The milliseconds to wait for new input on the handle

{- | Aborts the read attempt if one of the following holds:

   1. the timeout is up
        (= last update timestamp - start timestamp >= timeout)
   2. between last RS-update and last read with data more than 10% of
      timeout passed, AND
        some data was already read OR the waitForRead flag is not set

    This decision-tree is the reason why we call this ReadState 'Intelligent'
-}
instance ReadState IntelligentReadState where
    increment irs ngd =
        do
          ts <- getCurrentTime
          return $ if ngd then irs{ updated = ts, readtime = ts, hasread = ngd}
                          else irs{ updated = ts }
          
    abort (IRS to st lus slr gd b _) =
        to <= diffUTCTime lus st
               || ((not b || gd)
                   -- TODO: experiment with the 10 percent!
                   && let tr = diffUTCTime lus slr in tr > 0 && to / tr < 10)
    waitInp = waittimeInp

getOutput :: (ReadState a) => Handle -> a -> IO String
getOutput hdl rs = do
  s <- getOutput' rs hdl ""
  return $ reverse s

-- builds the string in the wrong order
-- tail-recursive function shouldn't make stack problems
getOutput' :: (ReadState a) => a -> Handle -> String -> IO String
getOutput' rs hdl s = do
  b <- if abort rs then return Nothing -- timeout gone
       -- eventually error on eof so abort
       else catch (liftM Just $ hWaitForInput hdl $ waitInp rs) $ const
                $ return Nothing
  case b of Nothing -> return s
            Just b' ->
                do
                  ns <- if b' then liftM (:s) $ hGetChar hdl else return s
                  nrs <- increment rs b'
                  getOutput' nrs hdl ns

-- | From given Time a ReadState is created and the output is fetched using
-- getOutput
getOutp :: Handle -> Int -> DTime -> IO String
getOutp hdl w t = initIRS w t True >>= getOutput hdl


-- ----------------------------------------------------------------------
-- * A Command Interface using the intelligent read state
-- ----------------------------------------------------------------------

-- | This is just a type to hold the information returned by
--  System.Process.runInteractiveCommand
data CommandState = CS { inp :: Handle, outp :: Handle, err :: Handle
                       , pid :: SP.ProcessHandle,  verbosity:: Int 
                       , tc :: TimeConfig }

-- | The IO State-Monad with state CommandState
type Command = IOS CommandState


-- | initialize the connection by running the given command string
start :: String -- ^ shell string to run the program
      -> Int    -- ^ Verbosity level
      -> Maybe TimeConfig
      -> IO CommandState
start shcmd v mTc = do
  when (v > 0) $ putStrLn $ "Running " ++ shcmd ++ " ..."
  (i,o,e,p) <- SP.runInteractiveCommand $ shcmd
  let cs = CS i o e p v $ fromMaybe defaultConfig mTc

  verbMessageIO cs 3 "start: Setting buffer modes"
  -- configure the handles 
  mapM_ (flip hSetBinaryMode False) [i, o, e]
  mapM_ (flip hSetBuffering NoBuffering) [o, e]
  hSetBuffering i LineBuffering
  -- clear all output from the output pipe (TIME: wait 300 milliseconds)
  verbMessageIO cs 3 "start: Clearing connection output."
  x <- getOutp o (waitForInp $ tc cs) $ startTimeout $ tc cs
  verbMessageIO cs 4 $ "start: Received\n--------------\n" ++ x
                    ++ "\n--------------"
  return cs

-- | Just read output from the connection waiting at most Time
readOutput :: DTime -> Command String
readOutput t = do
  s <- get
  liftIO $ getOutp (outp s) (waitForInp $ tc s) t

-- | Just read error output from the connection waiting at most Time
readErr :: DTime -> Command String
readErr t = do
  s <- get
  liftIO $ getOutp (err s) (waitForInp $ tc s) t

-- | Send some String and don't wait for response
send :: String -> Command ()
send str = do
  s <- get
  verbMessage s 2 $ "send: Sending " ++ str
  liftIO $ hPutStrLn (inp s) str

-- | Send some String and wait Time for response
call :: DTime   -- ^ Waits this time until abort call (Use float for seconds)
     -> String -- ^ Send this string over the connection
     -> Command String -- ^ Response
call t str = do
  s <- get
  -- first clear all output from the output pipe (wait 50 milliseconds)
  verbMessage s 3 "call: Clearing connection output."
  x <- liftIO $ getOutp (outp s) (waitForInp $ tc s) $ cleanTimeout $ tc s
  verbMessage s 4 $ "\n--------------\n" ++ x ++ "\n--------------"
  verbMessage s 2 $ "call: Sending " ++ str
  liftIO $ hPutStrLn (inp s) str
  res <- liftIO $ getOutp (outp s) (waitForInp $ tc s) t
  verbMessage s 2 $ "call: Received " ++ res
  return res


verbMessageIO :: CommandState -> Int -> String -> IO String
verbMessageIO cs v s = 
    if verbosity cs >= v then putStrLn s >> return s else return ""

verbMessage :: CommandState -> Int -> String -> Command String
verbMessage cs v s = liftIO $ verbMessageIO cs v s



-- | Send some exit command if there is one to close the connection.
-- This is the best one, but may be blocked by the application.
close :: Maybe String -> Command (Maybe ExitCode)
close str = do
  s <- get
  case str of Nothing -> do
                verbMessage s 3 "close: No exit command"
                return ()
              Just excmd -> do
                verbMessage s 2 $ "close: sending exit command: " ++ excmd
                liftIO $ hPutStrLn (inp s) excmd
  -- TODO: find out how to get the process id from the process handle
  verbMessage s 3 $ "close: waiting for process to terminate"
  e <- liftIO $ SP.waitForProcess $ pid s
  verbMessage s 2 $ "close: process exited with code " ++ show e
  return $ Just e

{-

-- Close variants:

-- | Send some exit command if there is one to close the connection
-- , and in addition terminate after wait
close2 :: Maybe String -> Command (Maybe ExitCode)
close2 str = do
  s <- get
  case str of Nothing -> do
                verbMessage s 3 "close: No exit command"
                return ()
              Just excmd -> do
                verbMessage s 2 $ "close: sending exit command: " ++ excmd
                liftIO $ hPutStrLn (inp s) excmd
  -- TODO: find out how to get the process id from the process handle
  verbMessage s 3 $ "close: waiting for process to terminate"
  e <- liftIO $ SP.waitForProcess $ pid s
  verbMessage s 2 $ "close: process exited with code " ++ show e
  verbMessage s 2 $ "close: forcing termination..."
  liftIO $ SP.terminateProcess $ pid s
  return $ Just e

-- | Send some exit command if there is one to close the connection
-- , but do not wait
close1 :: Maybe String -> Command (Maybe ExitCode)
close1 str = do
  s <- get
  case str of Nothing -> do
                verbMessage s 3 "close: No exit command"
                return ()
              Just excmd -> do
                verbMessage s 2 $ "close: sending exit command: " ++ excmd
                liftIO $ hPutStrLn (inp s) excmd
  -- TODO: find out how to get the process id from the process handle
  verbMessage s 3 $ "close: waiting for process to terminate"
  mE <- liftIO $ SP.getProcessExitCode $ pid s
  case mE of
    Just e -> do
              verbMessage s 2 $ "close: process exited with code " ++ show e
              return ()
    Nothing ->  do
              verbMessage s 2 $ "close: process did not terminate in time, "
                              ++ "forcing termination..."
              liftIO $ SP.terminateProcess $ pid s
  return mE

-}
