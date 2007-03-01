{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Network.Service
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- This module should, when completed allow functions of various types to be directly wrapped
-- up as a function of the form (Request -> IO Response), such that they can be published
-- as a web service function. The main function here is publish, which performs this
-- operation with the aid of GXS.
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
module Network.Service (HTTPTransport(..), soapCall) where

import Text.XML.Serializer
import Text.XML.HXT.Parser hiding (io)
import Text.XML.HXT.Aliases
import Org.Xmlsoap.Schemas.Soap.Envelope
import Network.HTTP
import Network.TCP
import Data.Maybe
import qualified Data.Map
import Data.Generics2
import Data.Dynamic
import Control.Monad.State
import Network.URI

type Config = Data.Map.Map String Dynamic

data PubFunc m = forall s . Service s m => PubFunc (s m)

soapTraceOn :: Bool
soapTraceOn = False

soapTrace x = (if soapTraceOn then putStrLn x else return ())

instance Service PubFunc m where
    publish c (PubFunc x) = publish c x

data MonadIO m => MonadFunc a b m = MonadFunc{mfunc::(Config -> a -> m b)}
data MonadIO m => SimpleFunc a b m = SimpleFunc{sfunc::(a -> b)}
data MonadIO m => XmlFunc m = XmlFunc{xfunc::Config -> XmlTrees -> m XmlTrees}

class Service s m where
    publish :: Config -> s m -> (XmlTrees -> m XmlTrees)

instance MonadIO m => Service XmlFunc m where
    publish c (XmlFunc f) = f c

instance (XMLNamespace a, XMLNamespace b, Data DictXMLData a, Data DictXMLData b, MonadIO m) 
    => Service (MonadFunc a b) m where
   publish c v = \xml -> do let Just m = (deserializeXML xml) :: Maybe (SimpleEnvelope a)
                                Body (Right i) = (body m)
                            o <- (mfunc v) c i
			    return $ (toXML (simpleEnvelope [] (Body $ Right o) Nothing) True)


instance (XMLNamespace a, XMLNamespace b, Data DictXMLData a, Data DictXMLData b, MonadIO m) 
    => Service (SimpleFunc a b) m where
    publish c (SimpleFunc f) = publish c (MonadFunc (\c -> return . f))

class MonadIO m => MonadUnIO i m o | m -> i o where
    -- | Drop the monad down to the inner monad.
    unliftIO :: i -> m a -> IO (a, o)
    -- | Recover the original monad and new state.
    reliftIO :: IO (a, o) -> m a
    -- | Get the input to the monad
    getMonadInput :: m i

instance MonadUnIO s (StateT s IO) s where
    unliftIO i m = runStateT m i
    reliftIO m = do (x, s) <- liftIO m
		    put s
		    return x
    getMonadInput = get


instance MonadUnIO () IO () where
    unliftIO i m = do x <- m
		      return (x, ())
    reliftIO m = do (x, _) <- m
		    return x
    getMonadInput = return ()

-- Client side service access

-- | Class for defining different methods of client-side service transport.
class ServiceTransport a where
    invokeTransport :: a -> String -> IO String

-- | A data-type for HTTP Transporation.
data HTTPTransport = HTTPTransport { httpEndpoint :: URI, httpSOAPAction :: Maybe URI } 

instance ServiceTransport HTTPTransport where
    invokeTransport (HTTPTransport ep act) dat = 
	do let hdrs = [Header HdrHost          (authority ep)
		      ,Header HdrContentType   "text/xml"
		      ,Header HdrContentLength (show $ length dat)
		      ,Header HdrUserAgent     "HAIFA"
		      ] ++
	              (maybe [] ((:[]) . Header (HdrCustom "SOAPAction") . show) act)			
           let req = Request ep POST hdrs dat	   
           rsp <- soapHTTP req
           either (fail . show) (\x -> return $ rspBody x) rsp

soapHTTP :: Request -> IO (Result Response)
soapHTTP r =
    do
       auth <- getAuth r
       let r' = fixReq auth r
       c <- openTCPPort (host auth) (fromMaybe 80 (port auth))
       rsp <- sendHTTP c r'
       close c
       return rsp
       where
             fixReq :: URIAuthority -> Request -> Request
	     fixReq URIAuthority{host=h} r = 
		 insertHeaderIfMissing HdrHost h $
		 r { rqURI = (rqURI r){ uriScheme = "", uriAuthority = Nothing } }	       

	     getAuth :: Monad m => Request -> m URIAuthority
	     getAuth r = case parseURIAuthority auth of
			 Just x -> return x 
			 Nothing -> fail $ "Error parsing URI authority '"
				           ++ auth ++ "'"
		 where auth = case findHeader HdrHost r of
			      Just h -> h
			      Nothing -> authority (rqURI r)

-- | Make a client-side SOAP Invocation, with a transport method, XML Hook and Input Message.
soapCall :: (Data DictXMLData (Envelope String String a), Data DictXMLData a, XMLNamespace a,
             Data DictXMLData (Envelope String String b), Data DictXMLData b, XMLNamespace b, ServiceTransport t) 
	    => t -> a -> IO (Either SimpleFault b)
soapCall t x = do let inEnv = toXMLString (simpleEnvelope [] (Body $ Right x) (Just "http://schemas.xmlsoap.org/soap/encoding/")) True
                  soapTrace "== Input Envelope ========================================"
                  soapTrace inEnv
                  soapTrace "=========================================================="                  
                  soapTrace "Performing call..."
                  o <- invokeTransport t inEnv                   
                  soapTrace "== Output Envelope ======================================="
                  soapTrace o
                  soapTrace "=========================================================="
		  xml <- parseXML o
		  e <- maybe (fail "Cannot parse SOAP Envelope using given type") return (xml >>= deserializeXML)
                  let h = (header e) :: [String]
                  return $ (fromBody $ body e)
