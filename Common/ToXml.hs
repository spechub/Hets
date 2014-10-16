{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{- |
Module      :  $Header$
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
myDataToXml d = case d of
  Builtin ty v -> if null v then unode ty () else unode ty v
  ListOrTuple b l -> let e = if b then "list" else "tuple" in
    if null l then unode e () else unode e $ map myDataToXml l
  Cons s mfs l -> if null l then unode s () else maybe
    (unode s $ case l of
      [Builtin ty v] -> add_attr (mkAttr ty v) $ unode s ()
      _ -> unode s $ map myDataToXml l)
    (eitherToElem s . zipWith (\ m f -> case m of
       Builtin _ v -> Left $ mkAttr f v
       _ -> Right $ myDataToXml m)
     l) mfs

class ToXml a where
  asXml :: a -> Element

instance Data a => ToXml a where
  asXml = myDataToXml . dataToMyData
