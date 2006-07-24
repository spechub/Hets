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
	    (	InjMap
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

-- * the data type of injective map

data InjMap a b = InjMap (Map.Map a b) (Map.Map b a) deriving Show

-- * the visible interface 

-- | gets an empty injective map
empty :: InjMap a b
empty = InjMap Map.empty Map.empty

-- | insert a pair to the given injective map. The existed key and the corresponding content would be overridden 
insert :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
--insert a b (InjMap m n) = InjMap (Map.insert a b m) (Map.insert b a n)
insert a b (InjMap m n) = case (Map.lookup a m) of
			       Just x -> insert a b (delete a x (InjMap m n))
			       Nothing -> case (Map.lookup b n) of
					     Just y -> insert a b (delete y b (InjMap m n))
					     Nothing -> InjMap (Map.insert a b m) (Map.insert b a n)

-- | delete the pair with the given keys in the injective map.
delete :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
delete a b (InjMap m n) = InjMap (Map.delete a m) (Map.delete b n) 

-- | transposing :)
transpose :: InjMap a b -> InjMap b a
transpose (InjMap n m) = (InjMap m n)

-- | look up the content with the given key in the direction of a->b in the injective map
lookupWithA :: (Ord a, Ord b) => a -> InjMap a b -> Maybe b
lookupWithA x (InjMap m n) = case (Map.lookup x m) of
				Just y -> 
				     case (Map.lookup y n) of
					Just temp -> 
					   if(temp==x) then Just y
					   else error "Common.InjMap.lookupWithA: the injectivity is destroyed" 
					Nothing -> error "Common.InjMap.lookupWithA: the inijectivity is destroyed"   
				Nothing -> Nothing

-- | look up the content with the given key in the direction of b->a in the injective map
lookupWithB :: (Ord a, Ord b) => b -> InjMap a b -> Maybe a
lookupWithB y (InjMap m n) = case (Map.lookup y n) of
				Just x -> 
				     case (Map.lookup x m) of
					Just temp ->
					   if(temp==y) then Just x
					   else error "InjMap.lookupWithA: the injectivity is destroyed"
					Nothing -> error "InjMap.lookupWithB: the inijectivity is destroyed"
				Nothing -> Nothing

-- | get the part of direction a->b in the map
getAToB :: (Ord a, Ord b) => InjMap a b -> Map.Map a b
getAToB (InjMap m n) = m

-- | get the part of direction b->a in the map
getBToA :: (Ord a, Ord b) => InjMap a b -> Map.Map b a
getBToA (InjMap m n) = n

-- | just for test :)
a :: InjMap Int String
a =  empty