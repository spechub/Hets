{-| 
   
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.HashMap where

import qualified IntMap as IntMap

data Map a b = Map (a -> Int) (IntMap.IntMap [(a, b)])

empty :: (k -> Int) -> Map k a
empty f = Map f IntMap.empty

lookup, luk :: Ord k => k -> Map k a -> Maybe a
lookup = luk
luk k (Map f im) = case IntMap.lookup (f k) im of
	     Nothing -> Nothing
	     Just mi -> Prelude.lookup k mi

findWithDefault :: Ord k => a -> k -> Map k a -> a
findWithDefault d k fm = maybe d id $ luk k fm

insert :: Ord k => k -> a -> Map k a -> Map k a
insert k e (Map f im) = 
    let ik = f k
    in case IntMap.lookup ik im of 
       Nothing -> Map f $ IntMap.insert ik [(k, e)] im
       Just l -> Map f $ IntMap.insert ik ((k, e): l) im
