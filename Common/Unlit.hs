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
unlit s = let cs = getCode True $ lines s in
  if all null cs then "" else unlines cs

-- keep code positions intact
getCode :: Bool -> [String] -> [String]
getCode d l = case l of
  [] -> []
  s : r -> if not d && isPrefixOf "\\end{code}" s
           || d && isPrefixOf "\\begin{code}" s
      then "" : getCode (not d) r
      else (case s of
      '>' : t | d -> ' ' : t
      _ -> if d then "" else s) : getCode d r
