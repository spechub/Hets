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








-- TESTPART:
-- 
-- h <- readFile "/tmp/Numbers.xml" >>= (\x -> return $ Hide $ Data.Maybe.fromJust $ parseXMLDoc x)

-- fmap (length . show . (filter (\x -> case x of (CRef _) -> True ; _ -> False)) . elContent) h

collectQNames :: (Set QName) -> Element -> (Set QName)
collectQNames s (Element q _ c _) = insert q $ unions $ Prelude.map (collectQNames s) $ onlyElems c

data Hide a = Hide a

instance Functor Hide where fmap f (Hide x) = Hide (f x)

instance Show a => Show (Hide a) where show (Hide x) = take 300 (show x)

theHidden :: (Hide a) -> a
theHidden (Hide x) = x
