{- |
Module      :  $Header$
Description :  Json utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2014
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

inspired by Yuriy Iskra's json2-types hackage package

-}

module Common.Json
  ( Json
  , ppJson
  , mkJStr
  , mkJBool
  , mkJNum
  , mkJArr
  , mkJObj
  , JPair
  , mkJPair
  , mkNameJPair
  , toJson
  , rangeToJPair
  , rangedToJson
  , anToJson
  , tagJson
  ) where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Result

import qualified Data.Map as Map
import Data.Char
import Data.List
import Data.Ratio

data Json
  = JString String
  | JNumber Rational
  | JBool Bool
  | JNull
  | JArray [Json]
  | JObject (Map.Map String Json)
    deriving (Eq, Ord)

type JPair = (String, Json)

showRat :: Rational -> String
showRat r = if denominator r == 1 then show $ numerator r else
  show (fromRational r :: Double)

-- use show to quote strings
instance Show Json where
  show j = case j of
    JString s -> show s
    JNumber r -> showRat r
    JBool b -> map toLower $ show b
    JNull -> "null"
    JArray js -> show js
    JObject m -> '{'
      : intercalate ","
        (map (\ (k, v) -> show k ++ ":" ++ show v)
        $ Map.toList m)
      ++ "}"

ppJson :: Json -> String
ppJson = show . pJ

pJ :: Json -> Doc
pJ j = case j of
  JArray js -> brackets . sep . punctuate comma $ map pJ js
  JObject m -> specBraces . sep . punctuate comma .
    map (\ (k, v) -> sep [text (show k), colon <+> pJ v]) $ Map.toList m
  _ -> text (show j)

mkJStr :: String -> Json
mkJStr = JString

mkJPair :: String -> String -> JPair
mkJPair a b = (a, mkJStr b)

mkNameJPair :: String -> JPair
mkNameJPair = mkJPair "name"

mkJNum :: Real b => b -> Json
mkJNum = JNumber . toRational

mkJBool :: Bool -> Json
mkJBool = JBool

toJson :: Pretty a => GlobalAnnos -> a -> Json
toJson ga a = mkJStr $ showGlobalDoc ga a ""

mkJObj :: [JPair] -> Json
mkJObj l = if null l then JNull else JObject $ Map.fromList l

mkJArr :: [Json] -> Json
mkJArr l = if null l then JNull else JArray l

rangeToJPair :: Range -> [JPair]
rangeToJPair rg = case rangeToList rg of
  [] -> []
  ps -> [mkJPair "range" . show $ prettyRange ps]

rangedToJson :: (GetRange a, Pretty a) => String -> GlobalAnnos -> a -> [JPair]
rangedToJson s ga a = (s, toJson ga a) : rangeToJPair (getRangeSpan a)

anToJson :: GlobalAnnos -> Annotation -> Json
anToJson ga = mkJObj . rangedToJson "annotation" ga

tagJson :: String -> Json -> Json
tagJson s j = mkJObj [(s, j)]
