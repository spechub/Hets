{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/OrderedMap.hs
Description :  ordered maps (these keep insertion order)
Copyright   :  (c)  Klaus Luettich and Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

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
  , null
  , lookup
  , insert
  , map, mapWithKey
  , update
  , filter, filterWithKey
  , partition, partitionWithKey, partitionMap
  , partitionMapWithKey, updateMapWithKey, notMember
  , mapMapKeys, insertLookupWithKey
  , fromList, toList
  , keys, elems
  ) where

import Prelude hiding (lookup, map, filter, null)

import Data.Data
import Data.Ord
import qualified Data.List as List
import qualified Data.HashMap.Strict as Map
import Data.Hashable

data ElemWOrd a = EWOrd
  { order :: Int
  , ele :: a }
  deriving (Show, Typeable, Data)

instance Ord a => Eq (ElemWOrd a) where
    x == y = compare x y == EQ

instance Ord a => Ord (ElemWOrd a) where
    compare = comparing ele

type OMap a b = Map.HashMap a (ElemWOrd b)

null :: (Ord k, Hashable k) => OMap k a -> Bool
null = Map.null

lookup :: (Monad m, Ord k, Hashable k) => k -> OMap k a -> m a
lookup k = maybe (fail "Common.OrderedMap.lookup")
  (return . ele) . Map.lookup k

insert :: (Ord k, Hashable k) => k -> a -> OMap k a -> OMap k a
insert k e m = Map.insertWith (\ ne oe -> oe {ele = ele ne})
               k (EWOrd (succ $ Map.size m) e) m

update :: (Ord k, Hashable k) => (a -> Maybe a) -> k -> OMap k a -> OMap k a
update = updateWithKey . const

updateWithKey :: (Ord k, Hashable k) => (k -> a -> Maybe a) -> k -> OMap k a -> OMap k a
updateWithKey f =
    updateMapWithKey $ \ k1 e -> case f k1 (ele e) of
                                         Nothing -> Nothing
                                         Just x -> Just e {ele = x}
filter :: (Ord k, Hashable k) => (a -> Bool) -> OMap k a -> OMap k a
filter = filterWithKey . const

filterWithKey :: (Ord k, Hashable k) => (k -> a -> Bool) -> OMap k a -> OMap k a
filterWithKey p = Map.filterWithKey (\ k -> p k . ele)

map :: (Ord k, Hashable k) => (a -> b) -> OMap k a -> OMap k b
map = mapWithKey . const

mapWithKey :: (Ord k, Hashable k) => (k -> a -> b) -> OMap k a -> OMap k b
mapWithKey f = Map.mapWithKey ( \ k x -> x {ele = f k (ele x)})

-- TODO: does this module make sense at all when using hash maps?

mapMapKeys :: (Ord k1, Hashable k1, Ord k2, Hashable k2) => 
              (k1 -> k2) -> Map.HashMap k1 a -> Map.HashMap k2 a
mapMapKeys kmap f = 
 foldl (\g (x, y) -> let x' = kmap x in Map.insert x' y g ) Map.empty $ Map.toList f


partition :: (Ord k, Hashable k) => (a -> Bool) -> OMap k a -> (OMap k a, OMap k a)
partition = partitionWithKey . const

partitionWithKey :: (Ord k, Hashable k) => (k -> a -> Bool) -> OMap k a
                 -> (OMap k a, OMap k a)
partitionWithKey p = partitionMapWithKey (\ k -> p k . ele)

partitionMap :: (Ord k, Hashable k) => (a -> Bool) -> Map.HashMap k a 
                       -> (Map.HashMap k a, Map.HashMap k a)
partitionMap test = partitionMapWithKey (\_ a -> test a)

partitionMapWithKey :: (Ord k, Hashable k) => (k -> a -> Bool) -> Map.HashMap k a 
                       -> (Map.HashMap k a, Map.HashMap k a)
partitionMapWithKey test f = 
 let flist = Map.toList f
     ylist = List.filter (\(x,y) -> test x y) flist
     nlist = List.filter (\(x,y) -> not $ test x y) flist
 in (Map.fromList ylist, Map.fromList nlist)

updateMapWithKey :: (Ord k, Hashable k) => 
  (k -> a -> Maybe a) -> k -> Map.HashMap k a -> Map.HashMap k a
updateMapWithKey test k f = 
 if not $ k `elem` Map.keys f then f
 else let v = Map.findWithDefault (error "updateMapWithKey") k f
      in case test k v of 
          Nothing -> Map.delete k f
          Just y -> Map.insert k y f

notMember :: (Ord k, Hashable k) => k -> Map.HashMap k a -> Bool
notMember k f = not $ k `elem` Map.keys f

insertLookupWithKey :: (Ord k, Hashable k) => 
  (k -> a -> a -> a) -> k -> a -> Map.HashMap k a -> 
  (Maybe a, Map.HashMap k a)
insertLookupWithKey f k a m = 
 let a' = Map.lookup k m
     m' = insertWithKey f k a m
 in (a', m')

insertWithKey :: (Ord k, Hashable k) => 
  (k -> a -> a -> a) -> k -> a -> Map.HashMap k a -> 
  Map.HashMap k a
insertWithKey f k a m = 
 if not (k `elem` Map.keys m) then Map.insert k a m
 else Map.insert k (f k a $ Map.findWithDefault (error "not possible") k m) m

fromList :: (Ord k, Hashable k) => [(k, a)] -> OMap k a
fromList = List.foldl ins Map.empty
    where ins m (k, e) = insert k e m

toList :: (Ord k, Hashable k) => OMap k a -> [(k, a)]
toList = List.map (\ (k, e) -> (k, ele e))
  . List.sortBy (comparing $ order . snd)
  . Map.toList

keys :: (Ord k, Hashable k) => OMap k a -> [k]
keys = List.map fst . toList

elems :: (Ord k, Hashable k) => OMap k a -> [a]
elems = List.map snd . toList
