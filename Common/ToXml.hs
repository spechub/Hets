{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
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

import Data.Data
import Data.Either
import Data.List

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

data BuiltinType = BStr | BChar | BBool | BNum

toTag :: BuiltinType -> String
toTag t = case t of
  BStr -> "string"
  BChar -> "char"
  BBool -> "bool"
  BNum -> "number"

data MyData = B BuiltinType String
  | ListOrTuple Bool [MyData] -- True means list
  | Cons String (Maybe [String]) [MyData] -- with optional field names

{- | convert to xml with special treatment for numbers, booleans, strings,
ranges, and other lists. -}
dataToMyData :: Data a => a -> MyData
dataToMyData a = let
    l = gmapQ dataToMyData a
    c = toConstr a
    fs = constrFields c
    s = showConstr c
    bool = const $ B BBool s :: Bool -> MyData
    res = case l of
      [] -> case s of
        "[]" -> ListOrTuple True []
        "()" -> ListOrTuple False []
        _ -> Cons s Nothing []
      [hd, ListOrTuple True rt] | s == "(:)" -> ListOrTuple True $ hd : rt
      _ | isPrefixOf "(," s -> ListOrTuple False l
      _ -> Cons s
        (if length fs == length l && all (not . null) fs
         then Just fs else Nothing) l
  in case dataTypeRep $ dataTypeOf a of
  r | elem r [IntRep, FloatRep] -> B BNum s
  CharRep -> B BChar s
  _ -> maybe
       (maybe
        (maybe res
         (B BStr . show . prettyRange) $ cast a)
       (B BStr) $ cast a) bool $ cast a

eitherToElem :: String -> [Either Attr Element] -> Element
eitherToElem s l = let (as, es) = partitionEithers l in
  add_attrs as $ unode s es

myDataToXml :: MyData -> Element
myDataToXml d = case d of
  B ty s -> unode (toTag ty) s
  ListOrTuple b l -> unode (if b then "list" else "tuple") $ map myDataToXml l
  Cons s mfs l -> maybe (unode s $ map myDataToXml l)
    (eitherToElem s . zipWith (\ m f -> case m of
       B _ v -> Left $ mkAttr f v
       _ -> Right $ myDataToXml m)
     l) mfs

class ToXml a where
  asXml :: a -> Element

instance Data a => ToXml a where
  asXml = myDataToXml . dataToMyData
