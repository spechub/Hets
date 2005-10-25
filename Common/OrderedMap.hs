{- | 
Module      :  $Header$
Copyright   :  (c)  Klaus Lüttich and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

ordered maps keep the ordering if converted from a list and of all
insert operations which are implemented; toList uses the
insertion\/conversion order for the creation of the new list

-}

module Common.OrderedMap ( OMap
                         , ElemWOrd(..)
                         , Map.empty, Map.null, Map.size
                         , Map.member
                         , lookup
                         , insert,insertWith,insertWithKey
                         , map, mapWithKey
                         , delete,(\\),difference
                         , filter, filterWithKey
                         , partition, partitionWithKey
                         , fromList, toList
                         , keys, Map.keysSet
                         ) where

import Prelude hiding (lookup,map,filter,foldr,foldl,null)

import qualified Common.Lib.Map as Map
import qualified Data.List as List
import Data.Maybe
import Control.Monad

infix 9 \\ -- add a comment for cpp

(\\) :: Ord k => OMap k a -> OMap k b -> OMap k a
m1 \\ m2 = difference m1 m2

data ElemWOrd a = EWOrd { order :: Int
                        , ele  :: a}
                deriving Show

instance Eq a => Eq (ElemWOrd a) where
    x == y = ele x == ele y

instance Ord a => Ord (ElemWOrd a) where
    compare x y = ele x `compare` ele y

type OMap a b = Map.Map a (ElemWOrd b)

lookup :: (Monad m,Functor m,Ord k) => k -> OMap k a -> m a
lookup k m = liftM ele $ Map.lookup k m

insert :: Ord k => k -> a -> OMap k a -> OMap k a
insert k e m = Map.insertWith (\ ne oe -> oe {ele = ele ne}) 
               k (EWOrd (Map.size m) e) m

insertWith :: Ord k => (a -> a -> a) -> k -> a -> OMap k a -> OMap k a 
insertWith f k e m = insertWithKey  (\ _k x y -> f x y) k e m

insertWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> OMap k a -> OMap k a
insertWithKey f k e m =
    Map.insertWithKey (\ k1 eo1 eo2 -> eo2 { ele = f k1 (ele eo1) (ele eo2)}) 
       k (EWOrd (Map.size m) e) m

delete :: Ord k => k -> OMap k a -> OMap k a
delete k m = 
    if Map.size dm == Map.size m 
       then dm
       else Map.map (updateOrder (order $ fromJust $ Map.lookup k m)) dm
    where dm = Map.delete k m
          updateOrder dOrder e 
              | order e < dOrder = e
              | order e == dOrder = error "Something strange happened" 
              | order e > dOrder = e { order = order e - 1}
              | otherwise = error "Never happens"

filter :: Ord k => (a -> Bool) -> OMap k a -> OMap k a
filter p = filterWithKey (\ _k x -> p x) 

filterWithKey :: Ord k => (k -> a -> Bool) -> OMap k a -> OMap k a
filterWithKey p = fromList . toList . Map.filterWithKey (\k e -> p k (ele e))

difference :: Ord k => OMap k a -> OMap k b -> OMap k a
difference m1 m2 = fromList $ toList $ Map.difference m1 m2

map :: Ord k => (a -> b) -> OMap k a -> OMap k b
map f = mapWithKey (\ _k x -> f x) 

mapWithKey :: (k -> a -> b) -> OMap k a -> OMap k b
mapWithKey f = Map.mapWithKey ( \ k x -> x {ele = f k (ele x)})

partition :: Ord k => (a -> Bool) -> OMap k a -> (OMap k a,OMap k a)
partition p = partitionWithKey (\ _k a -> p a)

partitionWithKey :: Ord k => (k -> a -> Bool) -> OMap k a 
                 -> (OMap k a,OMap k a)
partitionWithKey p m = case Map.partitionWithKey (\ k x -> p k (ele x)) m of
                       (x,y) -> (updateOrder x,updateOrder y)
    where updateOrder = fromList . toList

fromList :: Ord k => [(k,a)] -> OMap k a
fromList = List.foldl ins Map.empty
    where ins m (k,e) = insert k e m

toList :: Ord k => OMap k a -> [(k,a)]
toList = List.map (\ (k,e) -> (k,ele e)) . List.sortBy comp . Map.toList
    where comp (_,x) (_,y) = compare (order x) (order y) 

keys :: Ord k => OMap k a -> [k]
keys = List.map fst . toList
