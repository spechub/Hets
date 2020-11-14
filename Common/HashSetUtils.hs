{- |
Module      :  ./Common/HashSetUtils.hs
Description :  missing methods for hash sets
Copyright   :  (c) OVGU 2020
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable


-}

module Common.HashSetUtils where

import qualified Data.HashSet as Set
import Data.Hashable
import Data.List (foldl', sort)

partition :: (Eq a, Hashable a) => 
          (a -> Bool) -> Set.HashSet a -> (Set.HashSet a, Set.HashSet a)
partition test s = 
  foldl' (\(t, f) x -> if test x then (Set.insert x t, f) 
                       else (t, Set.insert x f)) 
  (Set.empty, Set.empty) $ Set.toList s

notMember :: (Eq a, Hashable a) => 
          a -> Set.HashSet a -> Bool
notMember a s = not $ Set.member a s

splitMember :: (Ord a, Hashable a) => 
            a -> Set.HashSet a -> (Set.HashSet a, Bool, Set.HashSet a)
splitMember a s = 
 foldl (\(l, b, g) x -> 
           case compare x a of
             LT -> (Set.insert x l, b, g)
             GT -> (l, b, Set.insert x g)
             EQ -> (l, True, g)) 
        (Set.empty, False, Set.empty) $ Set.toList s

findMin :: (Ord a, Hashable a) => 
        Set.HashSet a -> a 
findMin = 
 fst . deleteFindMin

findMax :: (Ord a, Hashable a) => 
        Set.HashSet a -> a 
findMax = fst . deleteFindMax

deleteMin :: (Ord a, Hashable a) => 
        Set.HashSet a -> Set.HashSet a
deleteMin = snd . deleteFindMin 

deleteMax :: (Ord a, Hashable a) => 
        Set.HashSet a -> Set.HashSet a
deleteMax = snd . deleteFindMax

deleteFindMin :: (Ord a, Hashable a) => 
        Set.HashSet a -> (a, Set.HashSet a)
deleteFindMin s = deleteFindAux False s

deleteFindMax :: (Ord a, Hashable a) => 
        Set.HashSet a -> (a, Set.HashSet a)
deleteFindMax s = deleteFindAux True s

deleteFindAux :: (Ord a, Hashable a) => 
        Bool -> Set.HashSet a -> (a, Set.HashSet a)
deleteFindAux b s =
 let l = sort $ Set.toList s
     l' = if b then reverse l else l
 in case l' of 
     [] -> error "no min elem in empty set"
     x:xs -> (x, Set.fromList xs)


