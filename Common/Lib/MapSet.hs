{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/Lib/MapSet.hs
Description :  Maps of sets
Copyright   :  (c) DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

supply total mappings from keys to sets of values based on Data.Map.
Undefined keys are mapped to the empty set. An abstract data type is needed
to avoid differences due to empty set values versus undefined map keys.

-}

module Common.Lib.MapSet
  ( rmNullSets
  , setLookup
  , setElems
  , setMember
  , setInsert
  , setAll
  , setDifference
  , setToMap
  , restrict
  , imageList
  , imageSet
  , MapSet
  , toMap
  , fromDistinctMap
  , fromMap
  , empty
  , null
  , fromList
  , toList
  , toPairList
  , keysSet
  , elems
  , insert
  , update
  , lookup
  , member
  , delete
  , union
  , difference
  , intersection
  , map
  , mapMonotonic
  , mapSet
  , foldWithKey
  , filter
  , partition
  , filterWithKey
  , all
  , isSubmapOf
  , preImage
  , transpose
  ) where

import Prelude hiding (all, filter, map, null, lookup)

import Data.Data
import Data.Hashable
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set
import qualified Data.List as List

-- * functions directly working over unwrapped maps of sets

-- | remove empty elements from the map
rmNullSets :: (Eq a, Hashable a, Eq b, Hashable b) => 
           Map.HashMap a (Set.HashSet b) -> Map.HashMap a (Set.HashSet b)
rmNullSets = Map.filter (not . Set.null)

-- | get elements for a key
setLookup :: (Eq a, Hashable a, Eq b, Hashable b) => 
          a -> Map.HashMap a (Set.HashSet b) -> Set.HashSet b
setLookup = Map.lookupDefault Set.empty

-- | all elementes united
setElems :: (Eq a, Hashable a, Eq b, Hashable b) => 
         Map.HashMap a (Set.HashSet b) -> Set.HashSet b
setElems = Set.unions . Map.elems

-- | test for an element under a key
setMember :: (Eq a, Hashable a, Eq b, Hashable b) => 
          a -> b -> Map.HashMap a (Set.HashSet b) -> Bool
setMember k v = Set.member v . setLookup k

-- | insert into a set of values
setInsert :: (Eq k, Hashable k, Eq a, Hashable a) => 
          k -> a -> Map.HashMap k (Set.HashSet a) ->
          Map.HashMap k (Set.HashSet a)
setInsert k v m = Map.insert k (Set.insert v $ setLookup k m) m

-- | update an element set under the given key
setUpdate :: (Eq k, Hashable k, Eq a, Hashable a) => 
  (Set.HashSet a -> Set.HashSet a) -> k
  -> Map.HashMap k (Set.HashSet a) -> Map.HashMap k (Set.HashSet a)
setUpdate f k m = let s = f $ setLookup k m in
  if Set.null s then Map.delete k m else Map.insert k s m

-- | test all elements of a set
setAll :: (Eq a, Hashable a) => (a -> Bool) -> Set.HashSet a -> Bool
setAll p = List.all p . Set.toList

-- | difference function for differenceWith, returns Nothing for empty sets
setDifference :: (Eq a, Hashable a) => Set.HashSet a -> Set.HashSet a -> Maybe (Set.HashSet a)
setDifference s t = let d = Set.difference s t in
    if Set.null d then Nothing else Just d

-- | convert a set into an identity map
setToMap :: (Eq a, Hashable a) => Set.HashSet a -> Map.HashMap a a
setToMap = Map.fromList . List.map (\ a -> (a, a)) . Set.toList

-- | restrict a map by a keys set
restrict :: (Eq k, Hashable k) => Map.HashMap k a -> Set.HashSet k -> Map.HashMap k a
restrict m = Map.intersection m . setToMap

-- | the image of a map
imageList :: (Eq k, Hashable k) => Map.HashMap k a -> Set.HashSet k -> [a]
imageList m = Map.elems . restrict m

-- | the image of a map
imageSet :: (Eq k, Hashable k, Eq a, Hashable a) => Map.HashMap k a -> Set.HashSet k -> Set.HashSet a
imageSet m = Set.fromList . imageList m

-- * protected maps of set as a newtype

-- | a map to non-empty sets
newtype MapSet a b = MapSet { toMap :: Map.HashMap a (Set.HashSet b) }
  deriving (Eq, Ord, Typeable, Data)

instance (Show a, Show b) => Show (MapSet a b) where
    show = show . toMap

instance (Eq a, Hashable a, Read a, 
          Eq b, Hashable b, Read b) => Read (MapSet a b) where
    readsPrec d = List.map (\ (m, r) -> (fromMap m , r)) . readsPrec d

-- | unsafe variant of fromMap (without removal of empty sets)
fromDistinctMap :: (Eq a, Hashable a, Eq b, Hashable b) => 
                Map.HashMap a (Set.HashSet b) -> MapSet a b
fromDistinctMap = MapSet

-- | remove empty values from the map before applying wrapping constructor
fromMap :: (Eq a, Hashable a, Eq b, Hashable b) => 
           Map.HashMap a (Set.HashSet b) -> MapSet a b
fromMap = MapSet . rmNullSets

-- | the empty relation
empty :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b
empty = MapSet Map.empty

-- | test for the empty mapping
null :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> Bool
null (MapSet m) = Map.null m

-- | convert from a list
fromList :: (Eq a, Hashable a, Eq b, Hashable b) => [(a, [b])] -> MapSet a b
fromList = fromMap
  . Map.fromListWith Set.union
  . List.map (\ (a, bs) -> (a, Set.fromList bs))

-- | convert to a list
toList :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> [(a, [b])]
toList = List.map (\ (a, bs) -> (a, Set.toList bs)) . Map.toList . toMap

toPairList :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> [(a, b)]
toPairList = concatMap (\ (c, ts) -> List.map (\ t -> (c, t)) ts) . toList

-- | keys for non-empty elements
keysSet :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> Set.HashSet a
keysSet = Set.fromList . Map.keys . toMap -- TODO: use HashSet?

-- | all elementes united
elems :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> Set.HashSet b
elems = setElems . toMap

-- | get elements for a key
lookup :: (Eq a, Hashable a, Eq b, Hashable b) => a -> MapSet a b -> Set.HashSet b
lookup k = setLookup k . toMap

-- | insert an element under the given key
insert :: (Eq a, Hashable a, Eq b, Hashable b) => a -> b -> MapSet a b -> MapSet a b
insert k v = MapSet . setInsert k v . toMap

-- | update an element set under the given key
update :: (Eq a, Hashable a, Eq b, Hashable b) => (Set.HashSet b -> Set.HashSet b) -> a -> MapSet a b
  -> MapSet a b
update f k = MapSet . setUpdate f k . toMap

-- | test for an element under a key
member :: (Eq a, Hashable a, Eq b, Hashable b) => a -> b -> MapSet a b -> Bool
member k v = setMember k v . toMap

-- | delete an element under the given key
delete :: (Eq a, Hashable a, Eq b, Hashable b) => a -> b -> MapSet a b -> MapSet a b
delete k v m@(MapSet r) = MapSet
  $ let s = Set.delete v $ lookup k m in
    if Set.null s then Map.delete k r else Map.insert k s r

-- | union of two maps
union :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> MapSet a b -> MapSet a b
union a b = MapSet . Map.unionWith Set.union (toMap a) $ toMap b

-- | difference of two maps
difference :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> MapSet a b -> MapSet a b
difference (MapSet m) = MapSet . Map.differenceWith setDifference m . toMap

-- | intersection of two maps
intersection :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> MapSet a b -> MapSet a b
intersection (MapSet m) = fromMap
  . Map.intersectionWith Set.intersection m . toMap

-- | map a function to all elements
map :: (Eq a, Hashable a, Eq b, Hashable b, Eq c, Hashable c) => (b -> c) -> MapSet a b -> MapSet a c
map f = MapSet . Map.map (Set.map f) . toMap

-- | unsafe map a function to all elements
mapMonotonic :: (Eq a, Hashable a, Eq b, Hashable b, Eq c, Hashable c) => (b -> c) -> MapSet a b -> MapSet a c
mapMonotonic f = MapSet . Map.map (Set.map f) . toMap -- TODO: leave as such for now, but does it make sense?

-- | apply a function to all element sets
mapSet :: (Eq a, Hashable a, Eq b, Hashable b, Eq c, Hashable c) => (Set.HashSet b -> Set.HashSet c) -> MapSet a b -> MapSet a c
mapSet f = fromMap . Map.map f . toMap

-- | fold over all elements
foldWithKey :: (Eq a, Hashable a, Eq b, Hashable b) => (a -> b -> c -> c) -> c -> MapSet a b -> c
foldWithKey f e = Map.foldrWithKey (\ a bs c -> Set.foldr (f a) c bs) e . toMap

-- | filter elements
filter :: (Eq a, Hashable a, Eq b, Hashable b) => (b -> Bool) -> MapSet a b -> MapSet a b
filter p = fromMap . Map.map (Set.filter p) . toMap

-- | partition elements
partition :: (Eq a, Hashable a, Eq b, Hashable b) => (b -> Bool) -> MapSet a b
  -> (MapSet a b, MapSet a b)
partition p m = (filter p m, filter (not . p) m)

-- | filter complete entries
filterWithKey :: (Eq a, Hashable a, Eq b, Hashable b) => (a -> Set.HashSet b -> Bool) -> MapSet a b -> MapSet a b
filterWithKey p = MapSet . Map.filterWithKey p . toMap

-- | test all elements
all :: (Eq a, Hashable a, Eq b, Hashable b) => (b -> Bool) -> MapSet a b -> Bool
all p = setAll p . elems

-- | submap test
isSubmapOf :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> MapSet a b -> Bool
isSubmapOf (MapSet m) = Map.isSubmapOfBy Set.isSubsetOf m . toMap

-- | pre-image of a map
preImage :: (Eq a, Hashable a, Eq b, Hashable b) => Map.HashMap a b -> MapSet b a
preImage = Map.foldrWithKey (flip insert) empty

-- | transpose a map set
transpose :: (Eq a, Hashable a, Eq b, Hashable b) => MapSet a b -> MapSet b a
transpose = foldWithKey (flip insert) empty

