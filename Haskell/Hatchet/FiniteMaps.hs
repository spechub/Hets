{-# OPTIONS -cpp #-}
{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

just a wrapper for the original interface

-}

module Haskell.Hatchet.FiniteMaps (FiniteMap, zeroFM, unitFM,
		   listToFM, listToCombFM, joinFM, joinCombFM, sizeFM,
		   Haskell.Hatchet.FiniteMaps.addToFM, 
		   addToCombFM, delFromFM, diffFM,
		   intersectFM, intersectCombFM, mapFM, foldFM,
		   filterFM, lookupFM, lookupDftFM, toListFM) where

import Data.FiniteMap

zeroFM :: Ord k => FiniteMap k e
zeroFM = emptyFM

listToCombFM :: Ord k => (e -> e -> e) -> [(k, e)] -> FiniteMap k e
listToCombFM c = addListToFM_C c emptyFM

addToFM :: Ord k => k -> e -> FiniteMap k e -> FiniteMap k e
addToFM k v m = Data.FiniteMap.addToFM m k v

addToCombFM :: Ord k
	       => (e -> e -> e) -> k -> e -> FiniteMap k e -> FiniteMap k e
addToCombFM f k v m = addToFM_C f m k v

joinFM :: Ord k => FiniteMap k e -> FiniteMap k e -> FiniteMap k e
joinFM = plusFM

joinCombFM :: Ord k 
	   => (e -> e -> e) -> FiniteMap k e -> FiniteMap k e -> FiniteMap k e
joinCombFM = plusFM_C

diffFM :: Ord k => FiniteMap k e -> FiniteMap k e -> FiniteMap k e
diffFM = minusFM

intersectCombFM :: Ord k
		=> (e -> e -> e) 
		-> FiniteMap k e 
		-> FiniteMap k e 
		-> FiniteMap k e
intersectCombFM = intersectFM_C

lookupDftFM :: Ord k => FiniteMap k e -> e -> k -> e
lookupDftFM = lookupWithDefaultFM 

toListFM :: Ord k => FiniteMap k e -> [(k, e)]
toListFM = fmToList

#if __GLASGOW_HASKELL__<=602
instance (Show k, Show a) => Show (FiniteMap k a) where
  showsPrec _ m  = showMap (fmToList m)
#endif

showMap :: (Show k,Show a) => [(k,a)] -> ShowS
showMap []     
  = showString "{}" 
showMap (x:xs) 
  = showChar '{' . showElem x . showTail xs
  where
    showTail []     = showChar '}'
    showTail (y:ys) = showChar ',' . showElem y . showTail ys
    showElem (k,v)  = shows k . showString ":=" . shows v
