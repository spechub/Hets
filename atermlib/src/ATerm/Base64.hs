{- |
Module      :  $Header$
Description :  Base64 character conversions
Copyright   :  (c) Ian Lynagh, 2005, 2007, Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

base64 character conversions
-}

module ATerm.Base64
  ( toBase64Int
  , toBase64Char
  , isBase64Char
  , ord0
  ) where

import Data.Char

{-
toBase64 :: [Char]
toBase64 =
  [ 'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/'
  ]
-}

toBase64Int :: Char -> Int
toBase64Int c
    | isUpper c = ord c - ordA
    | isLower c = ord c - i71
    | isDigit c = ord c + i4
    | c == '+' = 62
    | c == '/' = 63
    | otherwise = error "toBase64Int"

toBase64Char :: Int -> Char
toBase64Char i
    | i < 26 = chr (ordA + i)
    | i < 52 = chr (i71 + i)
    | i < 62 = chr (i - i4)
    | i == 62 = '+'
    | i == 63 = '/'
    | otherwise = error "toBase64Char"

isBase64Char :: Char -> Bool
isBase64Char c = isAscii c && (isAlphaNum c || c == '+' || c == '/')

-- a couple of constants

ordA :: Int
ordA = ord 'A'

i71 :: Int
i71 = ord 'a' - 26

ord0 :: Int
ord0 = ord '0'

i4 :: Int
i4 = 52 - ord0
