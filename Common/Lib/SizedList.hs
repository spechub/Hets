{- |
Module      :  $Header$
Description :  lists with their size similar to Data.Edison.Seq.SizedSeq
Copyright   :  C. Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

a list plus its length for a more efficient history implementation.
Parts of the implementation is stolen from Data.Edison.Seq.SizedSeq
-}

module SizedList where

import Prelude hiding (null, head, tail, reverse, take, drop)

import qualified Data.List as List

data SizedList a = N !Int [a] deriving (Show, Eq, Ord)

fromList :: [a] -> SizedList a
fromList xs = N (length xs) xs

toList :: SizedList a -> [a]
toList (N _ xs) = xs

empty :: SizedList a
empty = N 0 []

singleton :: a -> SizedList a
singleton x = N 1 [x]

cons :: a -> SizedList a -> SizedList a
cons x (N n xs) = N (succ n) $ x : xs

append :: SizedList a -> SizedList a -> SizedList a
append (N m xs) (N n ys) = N (m + n) $ xs ++ ys

head :: SizedList a -> a
head (N n xs) = case xs of
  x : _ | n > 0 -> x
  _ -> error "SizedList.head: empty list"

tail :: SizedList a -> SizedList a
tail (N n xs) = case xs of
  _ : r | n > 0 -> N (pred n) r
  _ ->  error "SizedList.tail: empty list"

null :: SizedList a -> Bool
null (N n _) = n == 0

size :: SizedList a -> Int
size (N n _) = n

reverse :: SizedList a -> SizedList a
reverse (N n xs) = N n (List.reverse xs)

take :: Int -> SizedList a -> SizedList a
take i original@(N n xs)
  | i <= 0 = empty
  | i >= n = original
  | otherwise = N i $ List.take i xs

drop :: Int -> SizedList a -> SizedList a
drop i original@(N n xs)
  | i <= 0 = original
  | i >= n = empty
  | otherwise = N (n - i) $ List.drop i xs
