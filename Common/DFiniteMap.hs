{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.DFiniteMap (
            -- * Map type
              Map          -- instance Eq,Show
            , EndoMap

            -- * Operators
            , (!), (\\)

            -- * Query
            , isEmpty
            , size
            , member
            , lookup
            , find          
            , findWithDefault
            
            -- * Construction
            , empty
            , single

            -- ** Insertion
            , insert
            , insertWith, insertWithKey, insertLookupWithKey

            -- ** Delete
            , delete

            -- * Combine

            -- ** Union
            , union         
            , unionWith          
            , unionWithKey

            -- ** Difference
            , difference
            
            -- ** Intersection
            , intersection           
            , intersectionWith

            -- * Traversal
            -- ** Map
            , map
            , mapWithKey
            
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

            -- ** Ordered lists
            , toAscList
            , fromAscList
            , fromDistinctAscList

            -- * Filter
            , filter
            , filterWithKey

	    ) where

import Data.FiniteMap
import Prelude hiding (lookup,map,filter)

infixl 9 !,\\

type Map a b = FiniteMap a b
type EndoMap a = FiniteMap a a


(!) :: Ord k => Map k a -> k -> a -- find
fm ! k = find k fm

(\\) :: Ord k => Map k a -> Map k a -> Map k a -- difference
m1 \\ m2 = difference m1 m2

isEmpty :: Map k a -> Bool
isEmpty = isEmptyFM

size :: Map k a -> Int
size = sizeFM

lookup :: Ord k => k -> Map k a -> Maybe a
lookup k fm = lookupFM fm k

member :: Ord k => k -> Map k a -> Bool
member = elemFM

find :: Ord k => k -> Map k a -> a
find k fm = maybe (error "mapping not found") (id) (lookupFM fm k)

findWithDefault :: Ord k => a -> k -> Map k a -> a
findWithDefault d k fm = lookupWithDefaultFM fm d k

empty :: Map k a
empty = emptyFM

single :: k -> a -> Map k a
single = unitFM

insert :: Ord k => k -> a -> Map k a -> Map k a
insert k e fm = addToFM fm k e

insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith cf k e fm = addToFM_C cf fm k e

insertWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithKey cf k e fm = addToFM_C (cf k) fm k e

insertLookupWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a,Map k a)
insertLookupWithKey cf k e fm = 
    (lookup k fm,addToFM_C (cf k) fm k e)

delete :: Ord k => k -> Map k a -> Map k a
delete k fm = delFromFM fm k

union :: Ord k => Map k a -> Map k a -> Map k a
union fm1 fm2 = plusFM fm2 fm1

unionWith :: Ord k => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith cf fm1 fm2 = plusFM_C cf fm2 fm1


unionWithKey :: Ord k => (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWithKey _cf _fm1 _fm2 = error "not implemented"

difference :: Ord k => Map k a -> Map k a -> Map k a
difference = minusFM

intersection :: Ord k => Map k a -> Map k a -> Map k a
intersection = intersectFM

intersectionWith :: Ord k => (a -> a -> a) -> Map k a -> Map k a -> Map k a
intersectionWith = intersectFM_C

filter :: Ord k => (a -> Bool) -> Map k a -> Map k a
filter f = filterFM (\_ e -> f e)

filterWithKey :: Ord k => (k -> a -> Bool) -> Map k a -> Map k a
filterWithKey = filterFM

map :: (a -> b) -> Map k a -> Map k b
map f = mapFM (\_ e -> f e)

mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
mapWithKey = mapFM

fold :: (a -> b -> b) -> b -> Map k a -> b
fold f = foldFM (\_ e b -> f e b)

foldWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
foldWithKey = foldFM

elems :: Map k a -> [a]
elems = eltsFM

keys  :: Map k a -> [k]
keys  = keysFM

assocs :: Map k a -> [(k,a)]
assocs = toList

fromList :: Ord k => [(k,a)] -> Map k a
fromList = listToFM

toList :: Map k a -> [(k,a)]
toList = fmToList

toAscList :: Map k a -> [(k,a)]
toAscList = toList

fromAscList :: (Ord k) => [(k,a)] -> Map k a
fromAscList = fromList 

fromDistinctAscList :: Ord k => [(k,a)] -> Map k a
fromDistinctAscList = fromList
