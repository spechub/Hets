{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{- |
Module      :  ./Common/ToXml.hs
Description :  xml utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

xml utilities on top of the xml light package and common hets data types
-}

module Common.ToXml where

import Common.AS_Annotation
import Common.Data
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Result

import Text.XML.Light

import Data.Data
import Data.Either

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

mkPriorityAttr :: String -> Attr
mkPriorityAttr = mkAttr "priority"

annotationF :: (Range -> [Attr]) -> GlobalAnnos -> Annotation -> Element
annotationF f ga a = add_attrs (f $ getRangeSpan a)
  $ prettyElem "Annotation" ga a

annotations :: GlobalAnnos -> [Annotation] -> [Element]
annotations = map . annotationF rangeAttrs

subnodes :: String -> [Element] -> [Element]
subnodes name elems = if null elems then [] else [unode name elems]

eitherToElem :: String -> [Either Attr Element] -> Element
eitherToElem s l = let (as, es) = partitionEithers l in
  add_attrs as $ unode s es

myDataToXml :: MyData -> Element
myDataToXml d =
  let
    listTag, listItemTag, dataItemTag :: String
    listTag = "List"
    listItemTag = "li"
    dataItemTag = "d"

    myDataToXmlWorker :: String -> MyData -> Element
    myDataToXmlWorker tag md = case md of
      Builtin _ v -> unode tag v
      ListOrTuple _ values ->
        unode tag $ map (myDataToXmlWorker listItemTag) values
      Cons _ Nothing values ->
        unode tag $ map (myDataToXmlWorker dataItemTag) values
      Cons _ (Just fields) values ->
        unode tag $ zipWith myDataToXmlWorker fields values
  in
    case d of
      Cons constructor _ _ -> myDataToXmlWorker constructor d
      ListOrTuple _ _ -> myDataToXmlWorker listTag d
      Builtin _ v -> unode dataItemTag v

class ToXml a where
  asXml :: a -> Element

instance {-# OVERLAPPABLE #-} Data a => ToXml a where
  asXml = myDataToXml . normalizeMyDataForSerialization . dataToMyData
