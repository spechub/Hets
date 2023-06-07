{-# LANGUAGE TypeSynonymInstances #-}
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
import qualified Xeno.DOM as Xeno
import Data.ByteString.UTF8 (toString)
import qualified Control.Monad.Fail as Fail

import qualified Data.ByteString as BS

readXmlFile :: FilePath -> IO BS.ByteString
readXmlFile fp = do
  bs <- BS.readFile fp
  if BS.length bs > 0 then return bs else
      Fail.fail "Common.XmlParser.readXmlFile: empty file"

parseXmlXeno :: BS.ByteString -> Either String Element
parseXmlXeno s = case Xeno.parse s of
  Left err -> Left $ show err
  Right nd -> let Elem e = xenoNodeToContent nd
    in Right e

xenoNodeToContent :: Xeno.Node -> Content
xenoNodeToContent nd =
  Elem $
    blank_element
      { elName = strToQName (Xeno.name nd),
        elAttribs = map attrToAttr (Xeno.attributes nd),
        elContent = xenoContentToContent (Xeno.contents nd)
      }

xenoContentToContent :: [Xeno.Content] -> [Content]
xenoContentToContent (Xeno.Text t : xs) = strToCData (toString t) : xenoContentToContent xs
xenoContentToContent (Xeno.CData t : xs) = strToCData (toString t) : xenoContentToContent xs
xenoContentToContent (Xeno.Element nd : xs) = xenoNodeToContent nd : xenoContentToContent xs
xenoContentToContent _ = []

strToCData :: String -> Content
strToCData s = Text $ blank_cdata { cdData = s }


attrToAttr :: (BS.ByteString, BS.ByteString) -> Attr
attrToAttr (n, v) = Attr { attrKey = strToQName n
                         , attrVal = toString v }

strToQName :: BS.ByteString -> QName
strToQName s = case break (':' ==) $ toString s of
                 (n, []) -> unqual n
                 (pr, _ : n) -> blank_name { qName = n, qPrefix = Just pr }

class XmlParseable a where
  parseXml :: a -> IO (Either String Element)

instance XmlParseable BS.ByteString where
  parseXml = return . parseXmlXeno