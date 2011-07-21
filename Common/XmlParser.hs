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


-- XML version from 1.3.7 on required!
-- TODO: specify in var.mk this requirement correctly, it is now required to have
-- exactly version 1.3.7 not >= 1.3.7.


#ifdef XML137
import Text.XML.Light
#else
import Text.XML.Light.Version_1_3_7_or_later_required
#endif

import qualified Data.ByteString.Lazy as BS
#ifdef HEXPAT
import qualified Common.XmlExpat as XE
#endif

readXmlFile :: FilePath -> IO BS.ByteString
readXmlFile = BS.readFile

{- | This class provides an xml parsing function which is instantiated
by using the hexpat or the XML.Light library, dependent on the haskell
environment. -}
class XmlParseable a where
    parseXml :: a -> Either String Element

#ifdef HEXPAT
instance XmlParseable BS.ByteString where
    parseXml = XE.parseXml

-- 169MB on Basic/Algebra_I
#else
instance XmlParseable BS.ByteString where
    parseXml s = case parseXMLDoc s of
                   Just x -> Right x
                   _ -> Left "parseXMLDoc: parse error"

-- 426MB on Basic/Algebra_I
#endif
