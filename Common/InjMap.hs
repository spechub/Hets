{- |
Module      :  $Header$
Description :  injective maps
Copyright   :  (c) Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Injective maps
-}

module Common.InjMap
    ( InjMap
    , unsafeConstructInjMap
    , getAToB
    , getBToA
    , empty
    , member
    , insert
    , delete
    , deleteA
    , deleteB
    , lookupWithA
    , lookupWithB
    , updateBWithA
    , updateAWithB
    ) where

import qualified Data.Map as Map

-- | the data type of injective maps
data InjMap a b = InjMap
    { getAToB :: Map.Map a b -- ^ the actual injective map
    , getBToA :: Map.Map b a -- ^ the inverse map
    } deriving (Show, Eq, Ord)

-- | for serialization only
unsafeConstructInjMap :: Map.Map a b -> Map.Map b a -> InjMap a b
unsafeConstructInjMap = InjMap

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

-- | delete domain entry
deleteA :: (Ord a, Ord b) => a -> InjMap a b -> InjMap a b
deleteA a i@(InjMap m n) = case Map.lookup a m of
  Just b -> case Map.lookup b n of
    Just e -> if e == a then InjMap (Map.delete a m) $ Map.delete b n
              else error "InjMap.deleteA1"
    Nothing -> error "InjMap.deleteA2"
  Nothing -> i

-- | delete codomain entry
deleteB :: (Ord a, Ord b) => b -> InjMap a b -> InjMap a b
deleteB b = transpose . deleteA b . transpose

-- | check membership of an injective pair
member :: (Ord a, Ord b) => a -> b -> InjMap a b -> Bool
member a b (InjMap m n) = case (Map.lookup a m, Map.lookup b n) of
   (Just x, Just y) | x == b && y == a -> True
   _ -> False

-- | transpose to avoid duplicate code
transpose :: InjMap a b -> InjMap b a
transpose (InjMap m n) = InjMap n m

-- | look up the content at domain
lookupWithA :: (Ord a, Ord b) => a -> InjMap a b -> Maybe b
lookupWithA a (InjMap m n) = case Map.lookup a m of
    Just b -> case Map.lookup b n of
        Just e -> if e == a then Just b
                     else error "InjMap.lookupWith1"
        Nothing -> error "InjMap.lookupWith2"
    Nothing -> Nothing
-- the errors indicate that the injectivity is destroyed

-- | look up the content at codomain
lookupWithB :: (Ord a, Ord b) => b -> InjMap a b -> Maybe a
lookupWithB y = lookupWithA y . transpose

-- | update codomain at domain value that must be defined
updateBWithA:: (Ord a, Ord b) => a  -> b -> InjMap a b -> InjMap a b
updateBWithA a b m = case lookupWithA a m of
    Nothing -> error "InjMap.updateBWithA"
    _ -> insert a b m

-- | update domain at codomain value that must be defined
updateAWithB :: (Ord a, Ord b) => b  -> a -> InjMap a b -> InjMap a b
updateAWithB b newA = transpose . updateBWithA b newA . transpose
