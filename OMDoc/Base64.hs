{- |
Module      :  $Header$
Description :  Base64 de- and encoding
Copyright   :  (c) Ian Lynagh, 2005, 2007, Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

copied from module Codec.Binary.Base64.String
of base64-string-0.1 and modified
-}

module OMDoc.Base64
  ( encode
  , decode
  ) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Char
import Data.Word
import ATerm.Base64

charsPerLine :: Int
charsPerLine = 64
-- PEM mandates 64. MIME allows anything up to 76.

splits :: Int -> [a] -> [[a]]
splits n xs = case xs of
  [] -> []
  _ -> case splitAt n xs of
         (ys, zs) -> ys : splits n zs

encode :: [Word8] -> String
encode = unlines . splits charsPerLine . enc

-- It is up to the caller to make sure the right sort of line breaks are
-- in the input
enc :: [Word8] -> String
enc str = case str of
  [] -> ""
  c1 : r1 -> let
    o1 = fromIntegral c1
    e1 = toBase64Char $ shiftR o1 2 -- First 6 bits of c1
    i2 = shiftL o1 4 .&. 0x30 -- Last 2 bits of c1
    in case r1 of
    [] -> e1 : toBase64Char i2 : "=="
    c2 : r2 -> let
      o2 = fromIntegral c2
      e2 = toBase64Char $ i2 .|. shiftR o2 4 -- First 4 bits of c2
      i3 = shiftL o2 2 .&. 0x3C -- Last 4 bits of c2
      in case r2 of
      [] -> e1 : e2 : toBase64Char i3 : "="
      c3 : r -> let
        o3 = fromIntegral c3
        e3 = toBase64Char $ i3 .|. shiftR o3 6 -- First 2 bits of c3
        e4 = toBase64Char $ o3 .&. 0x3F -- Last 6 bits of c3
        in e1 : e2 : e3 : e4 : enc r

decode :: String -> [Word8]
decode = dec . filter (\ c -> isBase64Char c || c == '=')

dec :: String -> [Word8]
dec str = case str of
  c1 : c2 : r2 | isBase64Char c1 && isBase64Char c2 ->
    case r2 of
      [] -> dec $ c1 : c2 : "=="
      e3 : r3 -> case r3 of
        [] -> dec $ c1 : c2 : e3 : "="
        e4 : r -> let
          (c3, c4) = if e3 == '=' then ('A', 'A') else
            if e4 == '=' then (e3, 'A') else (e3, e4)
          [x1, x2, x3, x4] = map toBase64Int [c1, c2, c3, c4]
          in -- 6 bits from x1, 2 bits from x2
             fromIntegral ((x1 `shiftL` 2) .|. (x2 `shiftR` 4))
             -- 4 bits from x2, 4 bits from x3
           : fromIntegral (((x2 `shiftL` 4) .&. 0xF0) .|. (x3 `shiftR` 2))
             -- 2 bits from x3, 6 bits from x4
           : fromIntegral (((x3 `shiftL` 6) .&. 0xC0) .|. x4)
           : dec r
  _ : r -> dec r -- invalid cases
  [] -> [] -- nothing left
