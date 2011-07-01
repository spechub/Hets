{- |
Module      :  $Header$
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
  ( MapSet
  , toMap
  , fromDistinctMap
  , rmNull
  , lookupSet
  , memberInSet
  , fromMap
  , empty
  , null
  , fromList
  , toList
  , insert
  , lookup
  , member
  , delete
  , union
  , difference
  , intersection
  , map
  , mapMonotonic
  , filter
  , isSubmapOf
  ) where

import Prelude hiding (filter, map, null, lookup)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

-- | a map to non-empty sets
newtype MapSet a b = MapSet { toMap :: Map.Map a (Set.Set b) }
  deriving (Eq, Ord)

instance (Show a, Show b) => Show (MapSet a b) where
    show = show . toMap

-- | unsafe variant of fromMap
fromDistinctMap :: Map.Map a (Set.Set b) -> MapSet a b
fromDistinctMap = MapSet

rmNull :: Ord a => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
rmNull = Map.filter (not . Set.null)

lookupSet :: Ord a => a -> Map.Map a (Set.Set b) -> Set.Set b
lookupSet = Map.findWithDefault Set.empty

-- | test for an element under a key
memberInSet :: (Ord a, Ord b) => a -> b -> Map.Map a (Set.Set b) -> Bool
memberInSet k v = Set.member v . lookupSet k

-- | remove empty values from the map
fromMap :: Ord a => Map.Map a (Set.Set b) -> MapSet a b
fromMap = MapSet . rmNull

-- | the empty relation
empty :: MapSet a b
empty = MapSet Map.empty

-- | test for the empty mapping
null :: MapSet a b -> Bool
null (MapSet m) = Map.null m

-- | convert from a list
fromList :: (Ord a, Ord b) => [(a, [b])] -> MapSet a b
fromList = fromMap
  . Map.fromListWith Set.union
  . List.map (\ (a, bs) -> (a, Set.fromList bs))

-- | convert to a list
toList :: MapSet a b -> [(a, [b])]
toList = List.map (\ (a, bs) -> (a, Set.toList bs)) . Map.toList . toMap

-- | insert an element under the given key
insert :: (Ord a, Ord b) => a -> b -> MapSet a b -> MapSet a b
insert k v = MapSet . Map.insertWith Set.union k (Set.singleton v) . toMap

-- | get elements for a key
lookup :: Ord a => a -> MapSet a b -> Set.Set b
lookup k = lookupSet k . toMap

-- | test for an element under a key
member :: (Ord a, Ord b) => a -> b -> MapSet a b -> Bool
member k v = memberInSet k v . toMap

-- | delete an element under the given key
delete :: (Ord a, Ord b) => a -> b -> MapSet a b -> MapSet a b
delete k v m@(MapSet r) = MapSet
  $ let s = Set.delete v $ lookup k m in
    if Set.null s then Map.delete k r else Map.insert k s r

-- | union of two maps
union :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> MapSet a b
union (MapSet m) (MapSet n) = MapSet
  $ Map.unionWith Set.union m n

-- | difference of two maps
difference :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> MapSet a b
difference (MapSet m) (MapSet n) = MapSet
  $ Map.differenceWith
    (\ s t -> let d = Set.difference s t in
              if Set.null d then Nothing else Just d) m n

-- | intersection of two maps
intersection :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> MapSet a b
intersection (MapSet m) = fromMap
  . Map.intersectionWith Set.intersection m . toMap

-- | map a function to all elements
map :: (Ord b, Ord c) => (b -> c) -> MapSet a b -> MapSet a c
map f = MapSet . Map.map (Set.map f) . toMap

-- | unsafe map a function to all elements
mapMonotonic :: (b -> c) -> MapSet a b -> MapSet a c
mapMonotonic f = MapSet . Map.map (Set.mapMonotonic f) . toMap

-- | filter elements
filter :: (Ord a, Ord b) => (b -> Bool) -> MapSet a b -> MapSet a b
filter p = fromMap . Map.map (Set.filter p) . toMap

-- | submap test
isSubmapOf :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> Bool
isSubmapOf (MapSet m) = Map.isSubmapOfBy Set.isSubsetOf m . toMap
