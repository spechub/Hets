{- |
Module      :  ./Static/AnalysisStructured.hs
Description :  A test module for trying API communication via sockets.
               The code is based on the TCP syslog server example in Real
               World Haskell.
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  mchan@inf.ed.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Grothendieck)

A test module for trying API communication via sockets. Use 'telnet <ip> <port>' to connect.
-}

import Data.Bits
import Network.Socket
import Network.BSD
import Data.List
import Control.Concurrent
import Control.Concurrent.MVar
import System.IO
import SyslogTypes
import Data.Maybe

type HandlerFunc = Maybe Handle -> SockAddr -> String -> IO ()

serveLog :: String              -- ^ Port number or name; 514 is default
         -> HandlerFunc         -- ^ Function to handle incoming messages
         -> IO ()
serveLog port handlerfunc = withSocketsDo $
    do -- Look up the port.  Either raises an exception or returns
       -- a nonempty list.
       addrinfos <- getAddrInfo
                    (Just (defaultHints {addrFlags = [AI_PASSIVE]}))
                    Nothing (Just port)
       let serveraddr = head addrinfos

       -- Create a socket
       sock <- socket (addrFamily serveraddr) Stream defaultProtocol

       -- Bind it to the address we're listening to
       bindSocket sock (addrAddress serveraddr)

       -- Start listening for connection requests.  Maximum queue size
       -- of 5 connection requests waiting to be accepted.
       listen sock 5

       -- Create a lock to use for synchronizing access to the handler
       lock <- newMVar ()

       -- Loop forever waiting for connections.  Ctrl-C to abort.
       procRequests lock sock

    where
          -- | Process incoming connection requests
          procRequests :: MVar () -> Socket -> IO ()
          procRequests lock mastersock =
              do (connsock, clientaddr) <- accept mastersock
                 handle lock Nothing clientaddr
                    "syslogtcpserver.hs: client connnected"
                 forkIO $ procMessages lock connsock clientaddr
                 procRequests lock mastersock

          -- | Process incoming messages
          procMessages :: MVar () -> Socket -> SockAddr -> IO ()
          procMessages lock connsock clientaddr =
              do connhdl <- socketToHandle connsock ReadWriteMode
                 hSetBuffering connhdl LineBuffering
                 messages <- hGetContents connhdl
                 mapM_ (handle lock (Just connhdl) clientaddr) (lines messages)
                 hClose connhdl
                 handle lock (Just connhdl) clientaddr
                    "syslogtcpserver.hs: client disconnected"

          -- Lock the handler before passing data to it.
          handle :: MVar () -> HandlerFunc
          -- This type is the same as
          -- handle :: MVar () -> Handle -> SockAddr -> String -> IO ()
          handle lock h clientaddr msg =
              withMVar lock
                 (\a -> handlerfunc h clientaddr msg >> return a)

syslog :: Maybe Handle -> Facility -> Priority -> String -> IO ()
syslog syslogh fac pri msg = case syslogh of
    Just h -> do hPutStrLn h sendmsg
                 -- Make sure that we send data immediately
                 hFlush h
              where
              sendmsg = msg
    _ -> return ()

-- A simple handler that prints incoming packets
plainHandler :: HandlerFunc
plainHandler h addr msg = do
    putStrLn $ "From " ++ show addr ++ ": " ++ msg
    syslog h USER INFO $ "Message received: " ++ msg
