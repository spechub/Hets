{- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

change an Xml-DGraph according to XmlDiff-data.
-}

module Static.ApplyXmlDiff where

import Common.XUpdate
--import Common.XSimplePath

import Control.Monad

import Text.XML.Light

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  foldM changeXml el cs

changeXml :: Monad m => Element -> Change -> m Element
changeXml el (Change csel expr) = case csel of
    Add _ addCs -> foldM insertXml el addCs where
      insertXml e' c = case c of
        AddElem e -> return e' { elContent = Elem e : elContent e' }
        _ -> fail $ "no implementation for " ++ show c
    Remove -> undefined
    _ -> fail $ "no implementation for " ++ show csel

