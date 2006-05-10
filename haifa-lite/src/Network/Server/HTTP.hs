{-# OPTIONS -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances -fth #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Network.Server.HTTP
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- I have stripped all the best bits out of HWS-WP and build a web server shell,
-- which essentially takes a list of handlers bound to URIs and uses them to 
-- construct a concrete web server.
--
-- This is a work in progress.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the 
-- GNU General Public License as published by the Free Software Foundation; either version 2 
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without 
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not, 
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Network.Server.HTTP where

import Network.HTTP
import Network.Stream
import Network.TCP
import Network.URI
import qualified Control.Exception as CE
import Network.BSD
import Network.Socket

import Data.Maybe
import Data.List
import Debug.Trace
import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception
import System.Directory
import System.Posix.Signals
import System.Exit
import Data.IORef
import System.IO
import Text.Html
import Text.Regex
import Text.XML.Serializer
import Text.XML.HXT.Parser (hasLocalPart, XmlTree, getChildren)
import Text.XML.HXT.Aliases
import Data.Dynamic
import qualified Data.Map
import Data.Generics2
import Org.W3.N2001.XMLSchema
import Text.XML.HXT.Parser (etag, (+=), txt)
--import Governor

data Conf = Conf { serverPort::Int }

data OptionKey a = OptKey String a deriving Typeable

-- | The server port key
serverPortKey = OptKey "serverPort" 8080 :: OptionKey Int

-- | A General Options map key
optionMapKey  = OptKey "anyOptions" (ElemSet [])

-- | The list of HTTP handlers stored in an MVar
httpHandlerKey = OptKey "httpHandlers" (error "HTTP Handler MVar must be defined by main IO Trunk" :: MVar [HTTPHandler])

-- | Get the list of HTTP Handlers from the Config file
getHTTPHandlers :: Config -> IO [HTTPHandler]
getHTTPHandlers c = readMVar (lookupOption httpHandlerKey c)

-- | Given a path the the config file and a list of option handlers (i.e. which take the XML Tree and mutate the configuration)
-- produce a configuration.
readOptions :: FilePath -> [[XmlTree] -> Config -> Config] -> IO Config
readOptions p fl = do f <- readFile p
		      x <- parseXML f
		      print x
		      case x of 
			     Nothing    -> fail "Could not parse config file."
			     Just []    -> fail "Invalid config file."
                             Just (x:_) -> return $ readOpts (getChildren x) fl Data.Map.empty
    where
    readOpts _ [] fm = fm
    readOpts xml (h:t) fm = readOpts xml t (h xml fm)

-- | Read a single option described by the given OptionKey from an XmlTree
getOption :: XMLData a => OptionKey a -> [XmlTree] -> Config -> Config
getOption (OptKey k d) ts fm = let n = case (concat $ map (hasLocalPart k) ts) of
			                   []    -> d 
			                   x     -> fromMaybe d $ deserializeXML x
						    in Data.Map.insert k (toDyn n) fm
type Config = Data.Map.Map String Dynamic

lookupOption :: Typeable a => OptionKey a -> Config -> a
lookupOption (OptKey k d) c = fromMaybe d (Data.Map.lookup k c >>= fromDynamic)

type HTTPHandler = (String, Config -> [String] -> Request -> IO (Either String Response))

-- | The server.
httpServer :: FilePath -> [HTTPHandler] -> [[XmlTree] -> Config -> Config] -> IO ()
httpServer p hnds ck = do    
    
    let ck' = ck ++ [getOption serverPortKey]

    hndRef <- newMVar hnds

    conf <- readOptions p ck' >>= \fm -> return $ Data.Map.insert "httpHandlers" (toDyn hndRef) fm



    --fc <- findM doesFileExist confLocations
    
    --let fc' = fromMaybe 
    --            (error "A Valid conf file could not be found, looked in "++(show confLocations)) fc
                
    
    -- conf <- loadConf fc'
    
    --tmp <- createPluginDir' (tmpPath conf)
    
    --conf <- return conf{tmpPath=tmp}
    
    --(hp, mp1) <- loadProtocols (protocolPath conf) tmp []
    --(ha, mp2) <- loadApps (appPath conf) tmp mp1
    --h <- initHAIFAEnv
    --henv <- run h $ haifaLoadTMDB (haifaPath ++ "tmdb.xml") >> getState
    -- f <- readFile "workingmodel.soap"
    -- x <- performRequest f "/Calculator" (HAC ha hp henv)
    -- print x
    -- return ()
    main_thread <- myThreadId
    installHandler sigINT (Catch (intHandler main_thread)) Nothing

    -- let conf = (Conf 5000)

    topServer conf --(HAC ha hp henv True)
    
    putStrLn "Bye Bye!"
    
topServer conf = do
    
    
    CE.catch (server conf) 
        (\x -> case x of
            CE.ErrorCall "**interrupted**" -> do
                                                putStrLn "HAC Closing down."
                                                --rmDir (tmpPath conf)
            y                              -> do
                                                  --putStrLn "Continues"
                                                  --print y
                                                  topServer conf
        )
    

intHandler :: ThreadId -> IO ()
intHandler t = CE.throwTo t (CE.ErrorCall "**interrupted**")

      
    
    
    
-- | The next 2 functions were ripped from HWS
--server :: HACConf -> HACEnv -> IO ()
server conf = do
  proto <- getProtocolNumber "tcp"
  hnds  <- getHTTPHandlers conf
  bracket
     (socket AF_INET Stream proto)
     (\sock -> sClose sock)
     (\sock -> do
        setSocketOption sock ReuseAddr 1
        bindSocket sock (SockAddrInet (fromIntegral (lookupOption serverPortKey conf)) iNADDR_ANY)
        listen sock maxListenQueue
        acceptConnections conf sock 
    )

-- | Accept connections, and fork off a new thread to handle each one
--acceptConnections :: HACConf -> HACEnv -> Socket -> IO ()
acceptConnections conf sock = do
  
  (h, sockAddr) <- accept sock

  let (SockAddrInet port haddr) = sockAddr

  hnds <- getHTTPHandlers conf

  forkIO ( (httpHandler conf hnds h sockAddr  `finally`  (shutdown h ShutdownBoth >> sClose h))
            `Control.Exception.catch`
          (\e -> trace ("servlet died: "  ++ show e) (return  ()))
    )

  acceptConnections conf sock

httpHandler :: Config -> [HTTPHandler] -> Socket -> SockAddr -> IO ()
httpHandler conf hnds s sa = do -- sendTo s "hello" sa
		         c <- newIORef $ MkConn s sa [] ""
	                 let conn = ConnRef c
                         rq <- receiveHTTP conn
		         {-print rq
		         case rq of
	                     Right r -> putStrLn $ rqBody r
		             Left _ -> return ()-}
                         case rq of 
				 Left  _ -> respond conn $ badRequest "Failed to parse HTTP Request! Whoops!"
				 Right r -> do let uri = (\x -> path x ++ query x ++ fragment x) $ rqURI r
					           f   = find (\(re, hnd) -> isJust $ matchRegex (mkRegex re) uri) hnds
					       case f of
						      Nothing    -> respond conn $ notFound ""
						      Just (re,h) -> do x <- h conf (fromJust $ matchRegex (mkRegex re) uri) r
								        case x of
									      Left  e -> respond conn $ internalServer e
									      Right x -> respond conn x

                         return ()

respond :: Stream s => s -> Response -> IO ()
respond conn r = let r' = if ((not $ null $ rspBody r) && (isNothing $ find (\(Header x _) -> x == HdrContentLength) $ rspHeaders r))
	                     then r{rspHeaders=(rspHeaders r)++[Header HdrContentLength (show $ length $ rspBody r)]}
			     else r
	                        in {-print r' >> putStrLn (rspBody r') >>-} respondHTTP conn r'

simpleHandler :: Config -> Request -> IO (Either String Response)
simpleHandler conf rq = do return (Right $ Response (2,0,0) "OK" [(Header HdrContentLength "5")] "hello")

badRequest b = Response (4,0,0) "Bad Request" [] $ htmlError "400 Bad Request" b
notFound b = Response (4,0,4) "Not Found" [] $ htmlError "404 Not Found" b
internalServer b = Response (5,0,0) "Internal Server Error" [] $ htmlError "500 Internal Server Error" b

publishViaGet :: String -> String -> Config -> [String] -> Request -> IO (Either String Response)
publishViaGet v t c m rq  = case (rqMethod rq) of
			     GET -> return (Right $ Response (2,0,0) "OK"
					                     [(Header HdrContentLength (show $ length v))
							     ,(Header HdrContentType t)] v)
			     _   -> return $ Right $ badRequest "This URL only supports GET"

responseOk = Response (2,0,0) "OK"

htmlError n b = renderHtml $ body $ ((h1 $ Html [HtmlString n]) +++ (paragraph $ stringToHtml b))

$(deriveTypeable [''Request, ''Response])
