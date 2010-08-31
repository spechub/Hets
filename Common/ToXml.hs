{- |
Module      :  $Header$
Description :  xml utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

xml utilities on top of the xml light package and common hets data types
-}

module Common.ToXml where

import Common.AS_Annotation
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Result

import Text.XML.Light

mkAttr :: String -> String -> Attr
mkAttr = Attr . unqual

mkText :: String -> Content
mkText s = Text $ CData CDataText s Nothing

prettyElem :: Pretty a => String -> GlobalAnnos -> a -> Element
prettyElem name ga a = unode name $ showGlobalDoc ga a ""

rangeAttrsF :: ([Pos] -> String) -> Range -> [Attr]
rangeAttrsF f rg = case rangeToList rg of
  [] -> []
  ps -> [mkAttr "range" $ f ps]

rangeAttrs :: Range -> [Attr]
rangeAttrs = rangeAttrsF $ show . prettyRange

mkNameAttr :: String -> Attr
mkNameAttr = mkAttr "name"

annotationF :: (Range -> [Attr]) -> GlobalAnnos -> Annotation -> Element
annotationF f ga a = add_attrs (f $ getRangeSpan a)
  $ prettyElem "Annotation" ga a

annotations :: GlobalAnnos -> [Annotation] -> [Element]
annotations = map . annotationF rangeAttrs

subnodes :: String -> [Element] -> [Element]
subnodes name elems = if null elems then [] else [unode name elems]
