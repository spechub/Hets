{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{- |
Module      :  ./Common/Json.hs
Description :  Json utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2014
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

inspired by Yuriy Iskra's json2-types hackage package

-}

module Common.Json
  ( Json (..)
  , ppJson
  , mkJStr
  , mkJBool
  , mkJNum
  , mkJArr
  , mkJObj
  , JPair
  , mkJPair
  , mkNameJPair
  , mkPriorityJPair
  , toJson
  , rangeToJPair
  , rangedToJson
  , anToJson
  , tagJson
  , pJson
  , ToJson (..)
  ) where

import Common.AS_Annotation
import Common.Data
import Common.Doc as Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.Id
import Common.Parsec
import Common.Result
import Common.Utils

import Data.Char
import Data.Data
import Data.List
import Data.Maybe
import Data.Ratio

import Numeric

import Text.ParserCombinators.Parsec

data Json
  = JString String
  | JNumber Rational
  | JBool Bool
  | JNull
  | JArray [Json]
  | JObject [JPair]
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
        (map (\ (k, v) -> show k ++ ":" ++ show v) m)
      ++ "}"

ppJson :: Json -> String
ppJson = show . pJ False

getOpBr :: Json -> Maybe Doc
getOpBr j = case j of
  JArray (j1 : _) -> Just $ lbrack <> fromMaybe empty (getOpBr j1)
  JObject _ -> Just lbrace
  _ -> Nothing

pJ :: Bool -> Json -> Doc
pJ omitOpBr j = case j of
  JArray js@(j1 : _) -> let md = getOpBr j1 in
    cat [ if omitOpBr then empty else lbrack <> fromMaybe empty md
        , sep (pJA (isJust md) js) ]
  JObject m -> sep [ if omitOpBr then empty else lbrace
    , sep . punctuate comma
      $ map (\ (k, v) -> let md = getOpBr v in
        cat [ text (show k) <> colon <+> fromMaybe empty md
            , Doc.space <> pJ (isJust md) v]) m
    , rbrace ]
  _ -> text (show j)

pJA :: Bool -> [Json] -> [Doc]
pJA omitOpBr l = case l of
  j1 : r@(j2 : _) -> let md = getOpBr j2 in
      (pJ omitOpBr j1 <> comma <+> fromMaybe empty md)
      : pJA (isJust md) r
  [j] -> [pJ omitOpBr j <> rbrack]
  [] -> []

mkJStr :: String -> Json
mkJStr = JString

mkJPair :: String -> String -> JPair
mkJPair a b = (a, mkJStr b)

mkNameJPair :: String -> JPair
mkNameJPair = mkJPair "name"

mkPriorityJPair :: String -> JPair
mkPriorityJPair = mkJPair "priority"

mkJNum :: Real b => b -> Json
mkJNum = JNumber . toRational

mkJBool :: Bool -> Json
mkJBool = JBool

toJson :: Pretty a => GlobalAnnos -> a -> Json
toJson ga a = mkJStr $ showGlobalDoc ga a ""

mkJObj :: [JPair] -> Json
mkJObj l = if null l then JNull else JObject l

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

pStr :: CharParser st String
pStr = do
  s <- getInput
  case reads s of
    [(s0, s1)] -> setInput s1 >> return s0
    _ -> pzero

pJBool :: CharParser st Json
pJBool = choice
  $ map (\ b -> let j = mkJBool b in string (show j) >> return j)
    [False, True]

pJNull :: CharParser st Json
pJNull = string (show JNull) >> return JNull

pJNumber :: CharParser st Json
pJNumber = do
  s <- getInput
  case readSigned readFloat s of
    [(n, s1)] -> setInput s1 >> return (JNumber n)
    _ -> pzero

pJson :: CharParser st Json
pJson = tok $ choice [fmap mkJStr pStr, pJBool, pJNull, pJNumber, pJArr, pJObj]

tok :: CharParser st a -> CharParser st a
tok p = p << spaces

cTok :: Char -> CharParser st ()
cTok = forget . tok . char

commaTok :: CharParser st ()
commaTok = cTok ','

pJArr :: CharParser st Json
pJArr = cTok '[' >> fmap JArray (sepBy1 pJson commaTok) << cTok ']'

pJObj :: CharParser st Json
pJObj = cTok '{' >> fmap JObject (sepBy1 pJPair commaTok) << cTok '}'

pJPair :: CharParser st JPair
pJPair = pair (tok pStr << cTok ':') pJson

{- | convert to json with special treatment for numbers, booleans, strings
and other lists. -}
myDataToJson :: MyData -> Json
myDataToJson md =
  let
    recordFieldToObject :: (String, MyData) -> (String, Json)
    recordFieldToObject (fieldName, value) =
      (toSnakeCase fieldName, myDataToJson value)
  in
    case md of
      Builtin typ value -> case typ of
        "number" -> case readSigned readFloat value of
          [(n, "")] -> JNumber n
          _ -> JString value
        "bool" | value == "True" -> JBool True
               | value == "False" -> JBool False
        "string" -> JString value
        _ -> JString value
      ListOrTuple _ mds -> JArray $ map myDataToJson mds
      -- Special cases
      Cons c Nothing [] | c `elem` ["Nothing", "Just", "Left", "Right"] ->
        error ("myDataToJson: Constructor should not have appeared: " ++ show c)
      -- Records
      Cons _ (Just fields) mds ->
        let
        in JObject $ zipWith (curry recordFieldToObject) fields mds
      -- Data types
      Cons constructor Nothing mds -> case map myDataToJson mds of
        [] -> JString constructor
        [e] -> e
        ijs -> JArray ijs

class ToJson a where
  asJson :: a -> Json

instance {-# OVERLAPPABLE #-} Data a => ToJson a where
  asJson = myDataToJson . normalizeMyDataForSerialization . dataToMyData
