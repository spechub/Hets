{-# LANGUAGE CPP, TypeSynonymInstances #-}
{- |
Module      :  ./Common/XmlParser.hs
Description :  Interface to the Xml Parsing Facility
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  portable

Provides an xml parse function which depends on external libraries.
-}


module Common.XmlParser (XmlParseable (parseXml), readXmlFile) where

import Text.XML.Light

import qualified Data.ByteString.Lazy as BS
#ifdef HEXPAT
import qualified Common.XmlExpat as XE
#else
import Data.ByteString.Lazy.UTF8
#endif

readXmlFile :: FilePath -> IO BS.ByteString
readXmlFile fp = do
  bs <- BS.readFile fp
  if BS.length bs > 0 then return bs else
      fail "Common.XmlParser.readXmlFile: empty file"

{- | This class provides an xml parsing function which is instantiated
by using the hexpat or the XML.Light library, dependent on the haskell
environment. -}
class XmlParseable a where
    parseXml :: a -> IO (Either String Element)

#ifdef HEXPAT
instance XmlParseable BS.ByteString where
    parseXml = return . XE.parseXml

-- 169MB on Basic/Algebra_I
#else
instance XmlParseable BS.ByteString where
    parseXml s = return $ case parseXMLDoc $ toString s of
                   Just x -> Right x
                   _ -> Left "parseXMLDoc: parse error"

-- 426MB on Basic/Algebra_I
#endif
