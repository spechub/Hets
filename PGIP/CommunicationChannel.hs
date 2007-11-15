{- |
Module      :$Header$
Description : communication channels handler for the CMDL interface
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.CommunicationChannels deals with handling socket opening and closing
and other channels like standard input or standard output

-}

module PGIP.CommunicationChannels

import Networking 
import Control.Exception 
import Control.Concurrent

openSocketConnection :: String -> Int -> CMDLState -> IO CMDLState
openSocketConnection name p
 = case find (\x ->  

-- | Opens the socket for reading data from the broker
openSocket :: Int -> IO (Socket,Handle, HostName, PortNumber)
openSocket port
 = 
   do
    -- open socket
    sock <- listenOn (PortNumber port)
    -- get handel for IO actions, hostName and portNumber
    (hnd, hstNm, pN) <- accept sock
    return (sock,hnd,hstNm,pN)

-- | Close the socket for reading 
closeSocket :: Socket -> Handle -> IO()
closeSocket sock hnd
   = do
       hClose hnd
       sClose sock

-- | opens a new connection 
openConnection :: String -> Int -> CMDLState ->IO CMDLState
openConnection name portNb state
 = case find (\x -> connName x == name) $ conns state of
    Nothing ->
     do
      (sck,hnd, hstNm, pNb) <- openSocket portNb
      let nwConn = CMDLSocket {
                     socket = sck,
                     handler = hnd,
                     hostName = hstNm,
                     portNumber = pNb,
                     connName = name
                     }
          cns = conns state
      return status {
                 conns = (cns:nwConn)
                 }
    Just _ -> return state { 
                        errorMsg = "Connection name already in use"
                        }

-- | get connection handler
getConnection :: String -> CMDLState -> Maybe Handle
getConnection name state
 = case find (\x -> connName x == name) $ conns state of
    Nothing -> Nothing
    Just sk -> Just (handler sk)


getConnectionHostName :: String -> CMDLState -> Maybe HostName
getConnectionHostName name state
 = case find (\x -> connName x == name) $ conns state of
    Nothing -> Nothing
    Just sk -> Just (hostName sk)

getConnectionPortNumber :: String -> CMDLState -> Maybe PortNumber
getConnectionPortNumber name state
 = case find (\x -> connName x == name) $ conns state of
    Nothing -> Nothing
    Just sk -> Just (portNumber sk)

getConnectionInfo :: String -> CMDLState 
                     -> Maybe (Handle, HostName,PortNumber)
getConnectionInfo name state
 = case find(\x -> connName x == name) $ conns state of
    Nothing -> Nothing
    Just sk -> Just (handler sk, hostName sk, portNumber sk)


closeConnection :: String -> CMDLState -> IO CMDLState
closeConnection name state
 = case find(\x -> connName x == name) $ conns state
    Nothing -> return state {
                        errorMsg = "Connection does not exist "
                        }
    Just sk -> do
                closeConnection (socket sk) (handler sk)
                return state {
                        conns = concatMap (\x -> if (connName x == name)
                                                  then []
                                                  else [x]) $ conns state
                             }
                                                  
