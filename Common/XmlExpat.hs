{- |
Module      :  $Header$
Description :  Interface to the Hexpat Library
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  portable

Provides the Hexpat parsing and transformation facility to XML.Light types.
-}


module Common.XmlExpat where

import qualified Data.ByteString.Lazy as BS
import qualified Text.XML.Expat.Tree as Expat

import Text.XML.Light


-- * Interface to the Expat xml parser

-- | Transforms an Expat xml tree to an XML.Light tree
nodesToContent :: [Expat.UNode String] -> [Content]
nodesToContent = nodesToContent' ""

-- | Version of 'nodesToContent' with accumulator to minimize the occurrences
-- of CData
nodesToContent' :: String -- ^ accumulates text nodes
                -> [Expat.UNode String] -- ^ list of content items
                -> [Content]
nodesToContent' s (Expat.Text t : xs) = nodesToContent' (s ++ t) xs
nodesToContent' s l
    | not $ null s = strToCData s : nodesToContent l
    | otherwise =
        case l of
          (Expat.Element { Expat.eName = n
                         , Expat.eAttributes = al, Expat.eChildren = cl } : xs)
              -> elemToElem n al cl : nodesToContent xs
          _ -> []

strToCData :: String -> Content
strToCData s = Text $ blank_cdata { cdData = s }


elemToElem :: String -> Expat.UAttributes String -> [Expat.UNode String]
           -> Content
elemToElem n al cl = Elem $ blank_element { elName = strToQName n
                                          , elAttribs = map attrToAttr al
                                          , elContent = nodesToContent cl }


attrToAttr :: (String, String) -> Attr
attrToAttr (n, v) = Attr { attrKey = strToQName n, attrVal = v }

strToQName :: String -> QName
strToQName s = case break (':' == ) s of
                 (_, []) -> unqual s
                 (pr, _ : n) -> blank_name { qName = n, qPrefix = Just pr }




parseXml :: BS.ByteString -> Either Element String
parseXml bs =
    let (nd, pe) = Expat.parse Expat.defaultParserOptions bs
        contl = nodesToContent [nd]
    in case pe of
         Just e -> Right $ "Expat.parse: " ++ show e
         _ -> case contl of
                [Elem e] -> Left e
                _ -> Right $ "Expat.parse: No unique root element."

