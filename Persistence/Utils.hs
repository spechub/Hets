module Persistence.Utils where

import Common.Utils (replace)

import Data.Char

parameterize :: String -> String
parameterize =
  dropDashes .
    mergeDashes False .
    map replaceSpecialChars .
    replace "=" "Eq" .
    map toLower
  where
    replaceSpecialChars :: Char -> Char
    replaceSpecialChars c = if ('A' <= c && c <= 'Z') ||
                               ('a' <= c && c <= 'z') ||
                               ('0' <= c && c <= '9')
                            then c
                            else '-'

    mergeDashes :: Bool -> [Char] -> [Char]
    mergeDashes _ [] = []
    mergeDashes previousWasDash (c:cs) =
      if previousWasDash
      then if c == '-'
           then mergeDashes True cs
           else c : mergeDashes False cs
      else if c == '-'
           then c : mergeDashes True cs
           else c : mergeDashes False cs

    dropDashes :: [Char] -> [Char]
    dropDashes = reverse . dropWhile (== '-') . reverse . dropWhile (== '-')
