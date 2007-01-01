{- |
Module      :  $Header$
Description :  injective maps
Copyright   :  (c) Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Injective maps
-}

module Common.InjMap
    ( InjMap
    , empty
    , member
    , insert
    , delete
    , lookupWithA
    , lookupWithB
    , getAToB
    , getBToA
    ) where

import qualified Common.Lib.Map as Map

-- | the data type of injective maps
data InjMap a b = InjMap
    { getAToB :: Map.Map a b -- ^ the part of direction a->b in the map
    , getBToA :: Map.Map b a -- ^ the part of direction b->a in the map
    } deriving (Show, Eq, Ord)

-- * the visible interface

-- | get an empty injective map
empty :: InjMap a b
empty = InjMap Map.empty Map.empty

{- | insert a pair into the given injective map. An existing key and the
corresponding content will be overridden. -}
insert :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
insert a b i = let InjMap m n = delete a b i in
    InjMap (Map.insert a b m) (Map.insert b a n)

{- | delete the pair with the given key in the injective
map. Possibly two pairs may be deleted if the pair is not a member. -}
delete :: (Ord a, Ord b) => a -> b -> InjMap a b -> InjMap a b
delete a b (InjMap m n) =
       InjMap (Map.delete (Map.findWithDefault a b n) $ Map.delete a m)
              (Map.delete (Map.findWithDefault b a m) $ Map.delete b n)

-- | check membership of an injective pair
member :: (Ord a, Ord b) => a -> b -> InjMap a b -> Bool
member a b (InjMap m n) = case (Map.lookup a m, Map.lookup b n) of
   (Just x, Just y) | x == b && y == a -> True
   _ -> False

-- | transpose to avoid duplicate code
transpose :: InjMap a b -> InjMap b a
transpose (InjMap m n) = InjMap n m

{- | look up the content with the given key in the direction of a->b
in the injective map. -}
lookupWithA :: (Ord a, Ord b) => a -> InjMap a b -> Maybe b
lookupWithA x (InjMap m n) = case Map.lookup x m of
    Just y -> case Map.lookup y n of
        Just temp -> if temp == x then Just y
                     else error "InjMap.lookupWith1"
        Nothing -> error "InjMap.lookupWith2"
    Nothing -> Nothing
-- the errors indicate that the inijectivity is destroyed

{- | look up the content with the given key in the direction of b->a
in the injective map. -}
lookupWithB :: (Ord a, Ord b) => b -> InjMap a b -> Maybe a
lookupWithB y = lookupWithA y . transpose
