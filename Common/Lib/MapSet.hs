{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
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
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import GHC.Generics (Generic)

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

-- | update an element set under the given key
setUpdate :: (Ord k, Ord a) => (Set.Set a -> Set.Set a) -> k
  -> Map.Map k (Set.Set a) -> Map.Map k (Set.Set a)
setUpdate f k m = let s = f $ setLookup k m in
  if Set.null s then Map.delete k m else Map.insert k s m

-- | test all elements of a set
setAll :: (a -> Bool) -> Set.Set a -> Bool
setAll p = List.all p . Set.toList

-- | difference function for differenceWith, returns Nothing for empty sets
setDifference :: Ord a => Set.Set a -> Set.Set a -> Maybe (Set.Set a)
setDifference s t = let d = Set.difference s t in
    if Set.null d then Nothing else Just d

-- | convert a set into an identity map
setToMap :: Ord a => Set.Set a -> Map.Map a a
setToMap = Map.fromDistinctAscList . List.map (\ a -> (a, a)) . Set.toList

-- | restrict a map by a keys set
restrict :: Ord k => Map.Map k a -> Set.Set k -> Map.Map k a
restrict m = Map.intersection m . setToMap

-- | the image of a map
imageList :: Ord k => Map.Map k a -> Set.Set k -> [a]
imageList m = Map.elems . restrict m

-- | the image of a map
imageSet :: (Ord k, Ord a) => Map.Map k a -> Set.Set k -> Set.Set a
imageSet m = Set.fromList . imageList m

-- * protected maps of set as a newtype

-- | a map to non-empty sets
newtype MapSet a b = MapSet { toMap :: Map.Map a (Set.Set b) }
  deriving (Eq, Ord, Typeable, Data, Generic)

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

toPairList :: MapSet a b -> [(a, b)]
toPairList = concatMap (\ (c, ts) -> List.map (\ t -> (c, t)) ts) . toList

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

-- | update an element set under the given key
update :: (Ord a, Ord b) => (Set.Set b -> Set.Set b) -> a -> MapSet a b
  -> MapSet a b
update f k = MapSet . setUpdate f k . toMap

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
union (MapSet m) = MapSet . Map.unionWith Set.union m . toMap

-- | difference of two maps
difference :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> MapSet a b
difference (MapSet m) = MapSet . Map.differenceWith setDifference m . toMap

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

-- | apply a function to all element sets
mapSet :: Ord a => (Set.Set b -> Set.Set c) -> MapSet a b -> MapSet a c
mapSet f = fromMap . Map.map f . toMap

-- | fold over all elements
foldWithKey :: (a -> b -> c -> c) -> c -> MapSet a b -> c
foldWithKey f e = Map.foldrWithKey (\ a bs c -> Set.fold (f a) c bs) e . toMap

-- | filter elements
filter :: (Ord a, Ord b) => (b -> Bool) -> MapSet a b -> MapSet a b
filter p = fromMap . Map.map (Set.filter p) . toMap

-- | partition elements
partition :: (Ord a, Ord b) => (b -> Bool) -> MapSet a b
  -> (MapSet a b, MapSet a b)
partition p m = (filter p m, filter (not . p) m)

-- | filter complete entries
filterWithKey :: Ord a => (a -> Set.Set b -> Bool) -> MapSet a b -> MapSet a b
filterWithKey p = MapSet . Map.filterWithKey p . toMap

-- | test all elements
all :: Ord b => (b -> Bool) -> MapSet a b -> Bool
all p = setAll p . elems

-- | submap test
isSubmapOf :: (Ord a, Ord b) => MapSet a b -> MapSet a b -> Bool
isSubmapOf (MapSet m) = Map.isSubmapOfBy Set.isSubsetOf m . toMap

-- | pre-image of a map
preImage :: (Ord a, Ord b) => Map.Map a b -> MapSet b a
preImage = Map.foldrWithKey (flip insert) empty

-- | transpose a map set
transpose :: (Ord a, Ord b) => MapSet a b -> MapSet b a
transpose = foldWithKey (flip insert) empty
