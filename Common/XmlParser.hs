{-# LANGUAGE CPP, TypeSynonymInstances #-}
{- |
Module      :  $Header$
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

#ifdef HEXPAT
import qualified Data.ByteString.Lazy as BS
import qualified Common.XmlExpat as XE
#else
#ifdef XMLBS
import qualified Data.ByteString.Lazy as BS
#endif
#endif


-- | This class provides an xml parsing function which is instantiated
-- by using the hexpat or the XML.Light library, dependent on the haskell
-- environment.
class XmlParseable a where
    parseXml :: a -> Either String Element


#ifdef HEXPAT
instance XmlParseable BS.ByteString where
    parseXml = XE.parseXml

readXmlFile :: FilePath -> IO BS.ByteString
readXmlFile = BS.readFile
-- 169MB on Basic/Algebra_I
#else

#ifdef XMLBS
instance XmlParseable BS.ByteString where
    parseXml s = case parseXMLDoc s of
                   Just x -> Right x
                   _ -> Left "parseXMLDoc: parse error"

readXmlFile :: FilePath -> IO BS.ByteString
readXmlFile = BS.readFile
-- 426MB on Basic/Algebra_I
#else
instance XmlParseable String where
    parseXml s = case parseXMLDoc s of
                   Just x -> Right x
                   _ -> Left "parseXMLDoc: parse error"

readXmlFile :: FilePath -> IO String
readXmlFile = readFile
-- 482MB on Basic/Algebra_I
#endif
#endif
