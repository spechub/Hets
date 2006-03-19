{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  portable

  some utility functions
-}
module OMDoc.Util where

import Char (isSpace)
import Data.List (isSuffixOf)

listStart::forall a . Eq a => [a]->[a]->Bool
listStart _ [] = True
listStart [] _ = False
listStart (l:ls) (x:lx) = (l==x) && (listStart ls lx)

isPrefix::forall a . Eq a => [a]->[a]->Bool
isPrefix [] _ = True
isPrefix _ [] = False
isPrefix (p:p' ) (s:s' ) = (p == s) && (isPrefix p' s')

contains::forall a . Eq a => [a]->[a]->Bool
contains [] [] = True
contains [] _ = False
contains l x = (listStart l x) || (contains (tail l) x)

implode::forall a . [a]->[[a]]->[a]
implode _ [] = []
implode _ [last' ] = last'
implode with (item:rest) = item ++ with ++ (implode with rest)
                        
-- explode byWhat list
-- TODO : this looks very slow...
explode::forall a . Eq a => [a]->[a]->[[a]]
explode by list =
  (\(p,q) -> p++[q]) $ foldl (\(exploded, current) newchar ->
    let
      newcurrent = current ++ [newchar]
    in
      if isSuffixOf by newcurrent
        then
          (exploded ++ [ take ((length newcurrent)-length(by)) newcurrent ], [])
        else
          (exploded, newcurrent)
  )
    ([],[])
    list

initorall::forall a . [a]->[a]
initorall [i] = [i]
initorall l = init l

-- | like init but returns empty list for empty list (init raises exception)
initOrEmpty::forall a . [a]->[a]
initOrEmpty [] = []
initOrEmpty l = init l

singleitem::forall a . Int->[a]->[a]
singleitem _ [] = []
singleitem 0 _ = []
singleitem 1 (i:_) = [i]
singleitem n (_:r) = singleitem (n-1) r

headorempty::forall a . [[a]]->[a]
headorempty [] = []
headorempty x = head x

tailorempty::forall a . [a]->[a]
tailorempty [] = []
tailorempty l = tail l

lastorempty::forall a . [a]->[a]
lastorempty [] = []
lastorempty l = [last l]

trim::(a->Bool)->[a]->[a]
trim test list = dropWhile test (reverse (dropWhile test (reverse list)))

trimString::String->String
trimString = trim (Char.isSpace)


