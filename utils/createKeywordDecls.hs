{- |
Module      :  $Id$
Description :  from a list of words create haskell constants
Copyright   :  (c) Christian Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

from a list of words (one each line) create haskell constants
-}

module Main where

import Data.Char
import qualified Data.Map as Map

main :: IO ()
main = getContents >>=
    mapM_ (\ (k, v) ->
         putStrLn ""
      >> putStrLn (k ++ " :: String")
      >> putStrLn (k ++ " = \"" ++ v ++ ":\""))
  . Map.toList
  . Map.fromList
  . map (\ s@(c : r) -> (toLower c : r ++ "C", s))
  . filter (not . null)
  . map (takeWhile $ \ c -> isAlpha c || c == '_')
  . lines
