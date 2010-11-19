{- |
Module      :  $Header$
Description :  unlit a source string
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a simple version to unlit a source string
-}

module Common.Unlit (unlit) where

import Data.List

unlit :: String -> String
unlit s = let cs = getCode False $ lines s in
  if all null cs then "" else unlines cs

-- keep code positions intact
getCode :: Bool -> [String] -> [String]
getCode c l = case l of
  [] -> []
  s : r
    | c && isPrefixOf "\\end{code}" s
      -> "" : getCode False r
    | c -> s : getCode c r
    | isPrefixOf "\\begin{code}" s
      -> "" : getCode True r
    | otherwise -> case s of
      '>' : t -> (' ' : t) : getCode c r
      _ -> "" : getCode c r
