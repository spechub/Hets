
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

supply the functions needed by Graph.hs

-}

module Common.Lib.SimpleMap (FiniteMap,  
                  emptyFM,addToFM,
                  updFM,                 -- applies function to stored entry
                  splitFM,               -- combines delFrom & lookup
                  delFromFM,
                  isEmptyFM,sizeFM,lookupFM,elemFM,
                  minFM,maxFM,
                  fmToList
                 ) where

import qualified Common.Lib.Map as Map

type FiniteMap = Map.Map
----------------------------------------------------------------------
-- MAIN FUNCTIONS
----------------------------------------------------------------------

emptyFM :: Ord a => FiniteMap a b
emptyFM = Map.empty

addToFM :: Ord a => FiniteMap a b -> a -> b -> FiniteMap a b
addToFM m a b = Map.insert a b m

updFM :: Ord a => FiniteMap a b -> a -> (b -> b) -> FiniteMap a b
updFM m k f = Map.update (Just . f) k m

delFromFM :: Ord a => FiniteMap a b -> a -> FiniteMap a b
delFromFM = flip Map.delete

isEmptyFM :: Ord a => FiniteMap a b -> Bool
isEmptyFM = Map.null

sizeFM :: Ord a => FiniteMap a b -> Int
sizeFM = Map.size

lookupFM :: Ord a => FiniteMap a b -> a -> Maybe b
lookupFM = flip Map.lookup


minFM :: Ord a => FiniteMap a b -> Maybe (a,b)
minFM m = if Map.null m then Nothing
          else Just $ Map.findMin m

maxFM :: Ord a => FiniteMap a b -> Maybe (a,b)
maxFM m = if Map.null m then Nothing
          else Just $ Map.findMax m

elemFM :: Ord a => FiniteMap a b -> a -> Bool
elemFM = flip Map.member

splitFM :: Ord a => FiniteMap a b -> a -> Maybe (FiniteMap a b, (a, b))
splitFM m a = case Map.lookup a m of
              Nothing -> Nothing
              Just b -> Just (Map.delete a m, (a, b))

fmToList :: Ord a => FiniteMap a b -> [(a,b)]
fmToList = Map.toList



                            
