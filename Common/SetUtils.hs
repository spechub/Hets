{- |
Module      :  $Header$
Description :  utils for singleton sets
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

utils for singleton sets that could also be part of "Data.Set". These
functions rely on 'Data.Set.size' being computable in constant time and
would need to be rewritten for set implementations with a size
function that is only linear.
-}

module Common.SetUtils where

import Data.Set

-- | /O(1)/ try to extract the element from a singleton set
lookupSingleton :: Set a -> Maybe a
lookupSingleton s = if size s == 1 then Just $ findMin s else Nothing 

-- | /O(1)/ test if the set's size is one
isSingleton :: Set a -> Bool
isSingleton s = size s == 1

-- | /O(1)/ comparison of the number with the set's size 
compareSize :: Int -> Set a -> Ordering
compareSize i = compare i . size

-- | /O(1)/ test if the set's size is greater one
hasMany :: Set a -> Bool
hasMany s = compareSize 1 s == LT
