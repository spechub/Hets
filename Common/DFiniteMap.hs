{-# OPTIONS -cpp #-}
{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (does -cpp on __GLASGOW_HASKELL__)

-}

module Common.DFiniteMap (
            -- * Map type
              Map          -- instance Eq,Show
            , EndoMap

            -- * Operators
            , (!) -- , (\\)

            -- * Query
            , isEmpty
            , size
            , member
            , lookup
            , find          
            , findWithDefault
            , findMin 
            , elemAt            

            -- * Construction
            , empty
            , single

            -- ** Insertion
            , insert
            , insertWith, insertWithKey, insertLookupWithKey
            , update
            , setInsert
            , listInsert

            -- ** Delete
            , delete

            -- * Combine

            -- ** Union
            , union         
            , unions         
            , unionWith          
            , unionWithKey

            -- ** Difference
            , difference
            , differenceWith
            , subset
            , differentKeys
            
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
            , partitionWithKey

            -- * Misc. additions
            , image
            , kernel

            ) where

import Data.FiniteMap
import Data.Maybe
import Data.List(foldl')
import Prelude hiding (lookup,map,filter)
import qualified Common.Lib.Set as Set

infixl 9 ! -- ,\\ 

type Map a b = FiniteMap a b
type EndoMap a = FiniteMap a a


(!) :: Ord k => Map k a -> k -> a -- find
fm ! k = find k fm

--(\\) :: Ord k => Map k a -> Map k a -> Map k a -- difference
--m1 \\ m2 = difference m1 m2

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

intersectionWith :: Ord k => (a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWith = intersectFM_C

filter :: Ord k => (a -> Bool) -> Map k a -> Map k a
filter f = filterFM (\_ e -> f e)

filterWithKey :: Ord k => (k -> a -> Bool) -> Map k a -> Map k a
filterWithKey = filterFM

partitionWithKey :: Ord k => (k -> a -> Bool) -> Map k a -> (Map k a, Map k a)
partitionWithKey p m = (filterFM p m, filterFM ( \ k v -> not $ p k v) m)

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

-- | Insert into a set of values
setInsert :: (Ord k, Ord a) => k -> a -> Map k (Set.Set a) -> Map k (Set.Set a)
setInsert  kx x t = case lookup kx t of
  Nothing -> insert kx (Set.single x) t
  Just xs -> insert kx (Set.insert x xs) t

-- | Insert into a list of values
listInsert :: Ord k => k -> a -> Map k [a] -> Map k [a]
listInsert  kx x t = case lookup kx t of
  Nothing -> insert kx [x] t
  Just xs -> insert kx (x:xs) t

-- | Difference with a combining function. 
differenceWith :: Ord k => (a -> a -> Maybe a) -> Map k a -> Map k a -> Map k a
differenceWith f m1 m2 = difference m1 m2 `union` 
    (map fromJust $ filter isJust $ intersectionWith f m1 m2)

subset :: (Ord k,Eq a) => Map k a -> Map k a -> Bool
subset m1 m2 = isEmpty $ 
    differenceWith ( \ a b -> if a == b then Nothing else Just a) m1 m2

-- | The expression (@update f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is @Nothing@, the element is
-- deleted. If it is (@Just y@), the key @k@ is bound to the new value @y@.
update :: Ord k => (a -> Maybe a) -> k -> Map k a -> Map k a
update f k m = case lookup k m of 
     Nothing -> m
     Just v -> case f v of 
	       Nothing -> delete k m
	       Just w -> insert k w m

-- | The union of a list of maps: (@unions == foldl union empty@).
unions :: Ord k => [Map k a] -> Map k a
unions ts = foldl' union empty ts

-- | find keys that are mapped differently
differentKeys :: (Ord k, Eq a) => Map k a -> Map k a -> [k]
differentKeys f1 f2 = keys $ filter id $ intersectionWith (/=) f1 f2 

-- | The minimal key of the map.
findMin :: Map k a -> (k,a)
findMin m = case toList m of
            [] -> error "Map.findMin: no minimal element"
            (x: _) -> x

{--------------------------------------------------------------------
  Image
--------------------------------------------------------------------}
image :: (Ord k, Ord a) => Map k a -> Set.Set k -> Set.Set a
image f s =
  Set.fold ins Set.empty s
  where ins x = case lookup x f of
                 Nothing -> id
                 Just y -> Set.insert y

{--------------------------------------------------------------------
  Kernel
--------------------------------------------------------------------}
kernel :: (Ord k, Eq a) => Map k a -> Set.Set (k,k)
kernel f = 
  Set.fromList [(k1,k2) | k1 <- keysF, k2 <- keysF, lookup k1 f == lookup k2 f]
  where keysF = keys f

{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
#if __GLASGOW_HASKELL__<=602
instance (Show k, Show a) => Show (FiniteMap k a) where
  showsPrec _ m  = showMap (toAscList m)
#endif

-- | Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
elemAt :: Int -> Map k a -> (k,a)
elemAt i m = toList m !! i

showMap :: (Show k,Show a) => [(k,a)] -> ShowS
showMap []     
  = showString "{}" 
showMap (x:xs) 
  = showChar '{' . showElem x . showTail xs
  where
    showTail []     = showChar '}'
    showTail (y:ys) = showChar ',' . showElem y . showTail ys
    showElem (k,v)  = shows k . showString ":=" . shows v
