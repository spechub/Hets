{- |
Module      :  $Id$
Description :  from a list of words create haskell constants
Copyright   :  (c) Christian Maeder, DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

from a list of words (one each line) create haskell constants
-}

module Main where

import Data.Char
import qualified Data.Map as Map

camelCase :: Bool -> String -> String
camelCase up s = case s of
  "" -> ""
  c : r -> if elem c "_-" then camelCase True r else
    [(if up then toUpper else toLower) c | isAlphaNum c]
    ++ camelCase False r

main :: IO ()
main = getContents >>=
    mapM_ (\ (k, v) ->
         putStrLn ""
      >> putStrLn (k ++ " :: String")
      >> putStrLn (k ++ " = \"" ++ v ++ "\""))
  . Map.toList
  . Map.fromList
  . map (\ s -> (camelCase False s ++ "S", s))
  . filter (not . null)
  . map (takeWhile $ \ c -> isAlpha c || elem c "-_?")
  . lines
