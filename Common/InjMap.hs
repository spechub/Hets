{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

injective maps
-}
module Common.InjMap
{-  ( 
            -- * Map type
              Map          -- instance Eq,Show

            -- * Operators
            , (!), (\\)


            -- * Query
            , null
            , size
            , member
            , lookup
            , findWithDefault
            
            -- * Construction
            , empty
            , singleton

            -- ** Insertion
            , insert
            , insertWith, insertWithKey, insertLookupWithKey
            
            -- ** Delete\/Update
            , delete
            , adjust
            , adjustWithKey
            , update
            , updateWithKey
            , updateLookupWithKey

            -- * Combine

            -- ** Union
            , union         
            , unionWith          
            , unionWithKey
            , unions
            , unionsWith

            -- ** Difference
            , difference
            , differenceWith
            , differenceWithKey
            
            -- ** Intersection
            , intersection           
            , intersectionWith
            , intersectionWithKey

            -- * Traversal
            -- ** Map
            , map
            , mapWithKey
            , mapAccum
            , mapAccumWithKey
            , mapKeys
            , mapKeysWith
            , mapKeysMonotonic

            -- ** Fold
            , fold
            , foldWithKey

            -- * Conversion
            , elems
            , keys
            , assocs
            
            -- ** Lists
            , toList
            , fromList
            , fromListWith
            , fromListWithKey

            -- ** Ordered lists
            , toAscList
            , fromAscList
            , fromAscListWith
            , fromAscListWithKey
            , fromDistinctAscList

            -- * Filter 
            , filter
            , filterWithKey
            , partition
            , partitionWithKey

            , split         
            , splitLookup   

            -- * Submap
            , isSubmapOf, isSubmapOfBy
            , isProperSubmapOf, isProperSubmapOfBy

            -- * Indexed 
            , lookupIndex
            , findIndex
            , elemAt
            , updateAt
            , deleteAt

            -- * Min\/Max
            , findMin
            , findMax
            , deleteMin
            , deleteMax
            , deleteFindMin
            , deleteFindMax
            , updateMin
            , updateMax
            , updateMinWithKey
            , updateMaxWithKey
            
            -- * Debugging
            , showTree
            , showTreeWith
            , valid
            ) -}
	    (
		InjMap
	      , empty
	      , insert
	      , delete
	      , transpose
	      , lookupWithA
	      , lookupWithB
	      , getAToB
	      , getBToA
	    )
            where

import qualified Common.Lib.Map as Map

data InjMap a b = InjMap (Map.Map a b) (Map.Map b a) deriving Show

empty :: InjMap a b
empty = InjMap Map.empty Map.empty

insert :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
--insert a b (InjMap m n) = InjMap (Map.insert a b m) (Map.insert b a n)
insert a b (InjMap m n) = case (Map.lookup a m) of
			       Just x -> insert a b (delete a x (InjMap m n))
			       Nothing -> case (Map.lookup b n) of
					     Just y -> insert a b (delete y b (InjMap m n))
					     Nothing -> InjMap (Map.insert a b m) (Map.insert b a n)

delete :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
delete a b (InjMap m n) = InjMap (Map.delete a m) (Map.delete b n) 

transpose :: InjMap a b -> InjMap b a
transpose (InjMap n m) = (InjMap m n)

lookupWithA :: (Ord a, Ord b) => a -> InjMap a b -> Maybe b
lookupWithA x (InjMap m n) = case (Map.lookup x m) of
				Just y -> 
				     case (Map.lookup y n) of
					Just temp -> 
					   if(temp==x) then Just y
					   else error "Common.InjMap.lookupWithA: the injectivity is destroyed" 
					Nothing -> error "Common.InjMap.lookupWithA: the inijectivity is destroyed"   
				Nothing -> Nothing

lookupWithB :: (Ord a, Ord b) => b -> InjMap a b -> Maybe a
lookupWithB y (InjMap m n) = case (Map.lookup y n) of
				Just x -> 
				     case (Map.lookup x m) of
					Just temp ->
					   if(temp==y) then Just x
					   else error "InjMap.lookupWithA: the injectivity is destroyed"
					Nothing -> error "InjMap.lookupWithB: the inijectivity is destroyed"
				Nothing -> Nothing

getAToB :: (Ord a, Ord b) => InjMap a b -> Map.Map a b
getAToB (InjMap m n) = m

getBToA :: (Ord a, Ord b) => InjMap a b -> Map.Map b a
getBToA (InjMap m n) = n


a :: InjMap Int String
a =  empty