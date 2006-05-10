{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fno-monomorphism-restriction #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Org.Xmlsoap.Schemas.Soap.Envelope
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- An implementation of the SOAP Envelope using the new Generic XML serializer.
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
module Org.Xmlsoap.Schemas.Soap.Envelope where

import Text.XML.Serializer
import Text.XML.Serializer.Derive
import Data.Typeable
import Data.Generics2
import Data.Dynamic
import Data.DynamicMap
--import Data.FiniteMap
import Data.Maybe
import Text.XML.HXT.Parser
import Text.XML.HXT.Aliases
import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Network.URI
import qualified Org.W3.N2001.XMLSchema as XSD
import qualified Org.W3.N2001.XMLSchema_instance as XSI

ghcNamespace = "Text.XML.Schema.Org.Xmlsoap.Schemas.Soap.Envelope"
thisNamespace = parseURI "http://schemas.xmlsoap.org/soap/envelope/"
tns = thisNamespace
soapPrefix = "soapenv"
                    
data Envelope h e a = 
         Envelope{ header        :: [h]
                 , body          :: Body e a
                 , encodingStyle :: Maybe String 
                 } deriving (Eq, Show)

type SimpleEnvelope x = Envelope String String x

simpleEnvelope :: [String] -> Body String a -> Maybe String -> SimpleEnvelope a
simpleEnvelope = Envelope

instance XMLNamespace (Envelope h e a) where
    namespaceURI _ = tns
    defaultPrefix _ = soapPrefix

-- How do we deal with SOAP Headers? There should be a finite (but expandable) number or understandable ones
-- which cause a SOAP Envelope parse to fail in some circumstances.
-- data Header   = forall a . (Typeable a, Data a) => Header a deriving (Typeable)

instance XMLNamespace (Body e a) where
    namespaceURI _ = tns
    defaultPrefix _ = soapPrefix

data Body e a = Body (Fault e `Either` a) deriving Show

fromBody (Body x) = x

instance XMLNamespace (Fault e) where
    namespaceURI _ = tns
    defaultPrefix _ = soapPrefix

type SimpleFault = Fault String
data Fault e = 
    Fault { faultcode   :: QName
          , faultstring :: String
          , faultactor  :: Maybe String
          , detail      :: Maybe e
          } deriving (Eq, Show)

-- Functions involving Unions aren't easily coerced to a type, because they involve strange classes.
simpleFault c s = Envelope [] (Body $ Left $ Fault (QN "" c "") s Nothing Nothing) Nothing

$(derive [''Envelope, ''Fault, ''Body])      

instance XSD.XSDType (Envelope h e a)
instance XSD.XSDType (Fault e)
instance XSD.XSDType (Body e a)

instance Error (Fault e) where
    noMsg  = Fault (QN "" "" "") "" Nothing Nothing
    strMsg x = Fault (QN "" "Error" "") x Nothing Nothing

instance (Data DictXMLData e, XMLNamespace e) => XMLData (Fault e) where
    toXMLType = deriveXMLType

instance (Data DictXMLData a, XMLNamespace a
         ,Data DictXMLData e, XMLNamespace e) => XMLData (Body e a) where
    toXMLType x = (deriveXMLType x) { fieldSchema = fieldsQ [\x -> ChildDefault] tns
                                    , isInterleaved = False
                                    }

instance (Data DictXMLData a, XMLNamespace a
         ,Data DictXMLData e, XMLNamespace e
         ,Data DictXMLData h, XMLNamespace h) => XMLData (Envelope h e a) where
    toXMLType x = (deriveXMLType x) { fieldSchema = fieldsQ [elmN occursAny  "Header", 
		          				     elmN occursOnce "Body", 
							     atr "encodingStyle"
							    ] tns
                                    , isInterleaved = True                             
                                    }

                                
{-
class SOAPTransport a where
    request_response :: (Data b, Data c) => 
                            a -> Serializer b -> Deserializer c -> SOAPEnvelope b -> IO (SOAPEnvelope c)
    one_way          :: (Data c) => a -> Serializer c -> SOAPEnvelope c -> IO ()
    solicit_response :: (Data c) => a -> Deserializer c -> IO SOAPEnvelope c
-}    
