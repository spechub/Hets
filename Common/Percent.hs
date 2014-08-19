{- |
Module      :  $Header$
Description :  precent encode and decode
Copyright   :  (c) Christian Maeder, DFKI GmbH 2014
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

precent encode or decode URLs, URIs and IRSs via UTF8
http://tools.ietf.org/html/rfc3986
-}

module Common.Percent
  ( encode
  , encodeBut
  , decode
  ) where

import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ByteString.Char8 as Char8
import Data.Char

{- according to http://tools.ietf.org/html/rfc3986#section-2.1
uppercase uppercase hexadecimal digits should be used -}
encodeChar8 :: (Char -> Bool) -> String -> String
encodeChar8 keep = concatMap $ \ c -> case c of
  _ | keep c -> [c]
  _ -> let (d, m) = divMod (ord c) 16 in
      '%' : map (toUpper . intToDigit) [d, m]

encodeBut :: (Char -> Bool) -> String -> String
encodeBut keep = encodeChar8 keep . Char8.unpack . UTF8.fromString

{- according to http://tools.ietf.org/html/rfc3986#section-2.3
unreserved characters should not be encoded -}
encode :: String -> String
encode = encodeBut $ \ c -> isAlphaNum c && isAscii c || elem c "_.-~"

decodeChar8 :: String -> String
decodeChar8 s = case s of
  "" -> ""
  '%' : x1 : x2 : r | isHexDigit x1 && isHexDigit x2
    -> chr (digitToInt x1 * 16 + digitToInt x2) : decodeChar8 r
  c : r -> c : decodeChar8 r

decode :: String -> String
decode = UTF8.toString . Char8.pack . decodeChar8
