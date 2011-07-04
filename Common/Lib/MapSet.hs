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
  ( setLookup
  , setElems
  , setMember
  , setInsert
  , MapSet
  , toMap
  , fromDistinctMap
  , fromMap
  , empty
  , null
  , fromList
  , toList
  , keysSet
  , elems
  , insert
  , lookup
  , member
  , delete
  , union
  , difference
  , intersection
  , map
  , mapMonotonic
  , foldWithKey
  , filter
  , isSubmapOf
  , preImage
  , transpose
  ) where

import Prelude hiding (filter, map, null, lookup)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

-- * functions directly working over unwrapped maps of sets

-- | remove empty elements from the map
rmNullSets :: Ord a => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
rmNullSets = Map.filter (not . Set.null)

-- | get elements for a key
setLookup :: Ord a => a -> Map.Map a (Set.Set b) -> Set.Set b
setLookup = Map.findWithDefault Set.empty

-- | all elementes united
setElems :: Ord b => Map.Map a (Set.Set b) -> Set.Set b
setElems = Set.unions . Map.elems

-- | test for an element under a key
setMember :: (Ord a, Ord b) => a -> b -> Map.Map a (Set.Set b) -> Bool
setMember k v = Set.member v . setLookup k

-- | insert into a set of values
setInsert :: (Ord k, Ord a) => k -> a -> Map.Map k (Set.Set a)
  -> Map.Map k (Set.Set a)
setInsert k v m = Map.insert k (Set.insert v $ setLookup k m) m

-- * protected maps of set as a newtype

-- | a map to non-empty sets
newtype MapSet a b = MapSet { toMap :: Map.Map a (Set.Set b) }
  deriving (Eq, Ord)

instance (Show a, Show b) => Show (MapSet a b) where
    show = show . toMap

instance (Ord a, Read a, Ord b, Read b) => Read (MapSet a b) where
    readsPrec d = List.map (\ (m, r) -> (fromMap m , r)) . readsPrec d

-- | unsafe variant of fromMap (without removal of empty sets)
fromDistinctMap :: Map.Map a (Set.Set b) -> MapSet a b
fromDistinctMap = MapSet

-- | remove empty values from the map before applying wrapping constructor
fromMap :: Ord a => Map.Map a (Set.Set b) -> MapSet a b
fromMap = MapSet . rmNullSets

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

-- | keys for non-empty elements
keysSet :: MapSet a b -> Set.Set a
keysSet = Map.keysSet . toMap

-- | all elementes united
elems :: Ord b => MapSet a b -> Set.Set b
elems = setElems . toMap

-- | get elements for a key
lookup :: Ord a => a -> MapSet a b -> Set.Set b
lookup k = setLookup k . toMap

-- | insert an element under the given key
insert :: (Ord a, Ord b) => a -> b -> MapSet a b -> MapSet a b
insert k v = MapSet . setInsert k v . toMap

-- | test for an element under a key
member :: (Ord a, Ord b) => a -> b -> MapSet a b -> Bool
member k v = setMember k v . toMap

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

-- | fold over all elements
foldWithKey :: (a -> b -> c -> c) -> c -> MapSet a b -> c
foldWithKey f e = Map.foldWithKey (\ a bs c -> Set.fold (f a) c bs) e . toMap

-- | filter elements
filter :: (Ord a, Ord b) => (b -> Bool) -> MapSet a b -> MapSet a b
filter p = fromMap . Map.map (Set.filter p) . toMap

-- | submap test
isSubmapOf :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> Bool
isSubmapOf (MapSet m) = Map.isSubmapOfBy Set.isSubsetOf m . toMap

-- | pre-image of a map
preImage :: (Ord a, Ord b) => Map.Map a b -> MapSet b a
preImage = Map.foldWithKey (\ k v -> insert v k) empty

-- | transpose a map set
transpose :: (Ord a, Ord b) => MapSet a b -> MapSet b a
transpose = foldWithKey (flip insert) empty
