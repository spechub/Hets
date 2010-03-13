{- |
Module      :  $Header$
Description :  ordered maps (these keep insertion order)
Copyright   :  (c)  Klaus Luettich and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Ordered maps (these keep insertion order)

ordered maps keep the ordering if converted from a list and of all
insert operations which are implemented; toList uses the
insertion\/conversion order for the creation of the new list

-}

module Common.OrderedMap
  ( OMap
  , ElemWOrd (..)
  , lookup
  , insert
  , map, mapWithKey
  , update
  , difference
  , filter
  , partition
  , fromList, toList
  , keys, elems
  ) where

import Prelude hiding (lookup, map, filter, null)

import qualified Data.Map as Map
import qualified Data.List as List

data ElemWOrd a = EWOrd
  { order :: Int
  , ele :: a }
  deriving Show

instance Ord a => Eq (ElemWOrd a) where
    x == y = compare x y == EQ

instance Ord a => Ord (ElemWOrd a) where
    compare x y = ele x `compare` ele y

type OMap a b = Map.Map a (ElemWOrd b)

lookup :: (Monad m, Ord k) => k -> OMap k a -> m a
lookup k = maybe (fail "Common.OrderedMap.lookup")
  (return . ele) . Map.lookup k

insert :: Ord k => k -> a -> OMap k a -> OMap k a
insert k e m = Map.insertWith (\ ne oe -> oe {ele = ele ne})
               k (EWOrd (succ $ Map.size m) e) m

update :: Ord k => (a -> Maybe a) -> k -> OMap k a -> OMap k a
update = updateWithKey . const

updateWithKey :: Ord k => (k -> a -> Maybe a) -> k -> OMap k a -> OMap k a
updateWithKey f =
    Map.updateWithKey $ \ k1 e -> case f k1 (ele e) of
                                         Nothing -> Nothing
                                         Just x -> Just e {ele = x}
filter :: Ord k => (a -> Bool) -> OMap k a -> OMap k a
filter = filterWithKey . const

filterWithKey :: Ord k => (k -> a -> Bool) -> OMap k a -> OMap k a
filterWithKey p = Map.filterWithKey (\ k -> p k . ele)

difference :: Ord k => OMap k a -> OMap k b -> OMap k a
difference = Map.difference

map :: Ord k => (a -> b) -> OMap k a -> OMap k b
map = mapWithKey . const

mapWithKey :: (k -> a -> b) -> OMap k a -> OMap k b
mapWithKey f = Map.mapWithKey ( \ k x -> x {ele = f k (ele x)})

partition :: Ord k => (a -> Bool) -> OMap k a -> (OMap k a, OMap k a)
partition = partitionWithKey . const

partitionWithKey :: Ord k => (k -> a -> Bool) -> OMap k a
                 -> (OMap k a, OMap k a)
partitionWithKey p = Map.partitionWithKey (\ k -> p k . ele)

fromList :: Ord k => [(k, a)] -> OMap k a
fromList = List.foldl ins Map.empty
    where ins m (k, e) = insert k e m

toList :: Ord k => OMap k a -> [(k, a)]
toList = List.map (\ (k, e) -> (k, ele e)) . List.sortBy comp . Map.toList
    where comp (_, x) (_, y) = compare (order x) (order y)

keys :: Ord k => OMap k a -> [k]
keys = List.map fst . toList

elems :: Ord k => OMap k a -> [a]
elems = List.map snd . toList
