{- |
Module      :  $Header$
Description :  OMDoc-to-XML conversion
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Implementation of the OMDoc-Datatype to XML transformation, there and back
-}

module OMDoc.XmlInterface
  where

import OMDoc.DataTypes
import Text.XML.Light
import Data.Set
import Data.Maybe

-- | The implemented OMDoc version
omdoc_current_version :: String
omdoc_current_version = "1.2"

-- | often used element names
el_omdoc, el_theory, el_view, el_axiom, el_theorem, el_symbol, el_import :: QName

el_omdoc = (blank_name { qName = "omdoc" })
el_theory = (blank_name { qName = "theory" })
el_view = (blank_name { qName = "view" })
el_axiom = (blank_name { qName = "axiom" })
el_theorem = (blank_name { qName = "theorem" })
el_symbol = (blank_name { qName = "symbol" })
el_import = (blank_name { qName = "import" })

el_fmp, el_omobj :: QName

el_fmp = (blank_name { qName = "FMP" })
el_omobj = (blank_name { qName = "OMOBJ" })

el_axiom_or_theorem :: Bool -> QName
el_axiom_or_theorem True = el_axiom
el_axiom_or_theorem False = el_theorem

-- | often used attribute names
at_id, at_version :: QName

at_id = (blank_name { qName = "id", qPrefix = Just "xml" })
at_version = (blank_name { qName = "version" })
at_cd = (blank_name { qName = "cd" })
at_name = (blank_name { qName = "name" })


class XmlRepresentable a where
  -- | render instance to an XML Element
  toXml :: a -> Element
  -- | reader instance from an XML Element
  fromXml :: Element -> Maybe a

listToXml :: XmlRepresentable a => [a] -> [Content]
listToXml l = Prelude.map (Elem . toXml) l

listFromXml :: XmlRepresentable a => [Content] -> [a]
listFromXml elems = catMaybes $ Prelude.map fromXml (onlyElems elems)

instance XmlRepresentable OMDoc where
    toXml (OMDoc id elems) = 
        (Element el_omdoc
         [Attr at_version omdoc_current_version, Attr at_id id]
         (listToXml elems)
         Nothing)
    fromXml (Element n a c _)
        | n == el_omdoc = 
            Nothing
        | otherwise = Nothing


instance XmlRepresentable TLElement where
    toXml (TLTheory id elems) = 
        (Element el_theory
         [Attr at_id id]
         (listToXml elems)
         Nothing)
    toXml TLView = 
        (Element el_view
         []
         []
         Nothing)
    fromXml (Element n a c _)
        | n == el_theory = 
            Nothing
        | n == el_view = 
            Nothing
        | otherwise = Nothing

instance XmlRepresentable TCElement where
    toXml (TCAxiomOrTheorem b id obj) = 
        (Element (el_axiom_or_theorem b) [Attr at_id id]
         [Elem $ Element el_fmp []
          [Elem $ Element el_omobj []
            [Elem $ toXml obj]
            Nothing]
          Nothing]
         Nothing)
    toXml (TCSymbol id symtype) = 
        (Element el_symbol
         [Attr at_name id]
         [Elem $ toXml symtype]
         Nothing)
    toXml TCImport = 
        (Element el_import
         []
         []
         Nothing)
    fromXml (Element n a c _)
        | n == el_axiom = 
            Nothing
        | n == el_theorem = 
            Nothing
        | n == el_symbol = 
            Nothing
        | n == el_import = 
            Nothing
        | otherwise = Nothing
                                  


instance XmlRepresentable OMElement where
    toXml _ = blank_element
    fromXml _ = Nothing


-- TESTPART:
-- 
-- h <- readFile "/tmp/Numbers.xml" >>= (\x -> return $ Hide $ Data.Maybe.fromJust $ parseXMLDoc x)

-- fmap (length . show . (filter (\x -> case x of (CRef _) -> True ; _ -> False)) . elContent) h

collectQNames :: (Set QName) -> Element -> (Set QName)
collectQNames s (Element q _ c _) = insert q $ unions $ Prelude.map (collectQNames s) $ onlyElems c

allQNames :: Element -> [QName]
allQNames e = Data.Set.toList $ collectQNames Data.Set.empty e

getXml :: String -> IO Element
getXml s = readFile s >>= (return . Data.Maybe.fromJust . parseXMLDoc)


data Hide a = Hide a

instance Functor Hide where fmap f (Hide x) = Hide (f x)

instance Show a => Show (Hide a) where show (Hide x) = take 300 (show x)

theHidden :: (Hide a) -> a
theHidden (Hide x) = x
