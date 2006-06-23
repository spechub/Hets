{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

injective maps
-}
module Common.InjMap
{-  ( 
            -- * Map type
              Map          -- instance Eq,Show

            -- * Operators
            , (!), (\\)


            -- * Query
            , null
            , size
            , member
            , lookup
            , findWithDefault
            
            -- * Construction
            , empty
            , singleton

            -- ** Insertion
            , insert
            , insertWith, insertWithKey, insertLookupWithKey
            
            -- ** Delete\/Update
            , delete
            , adjust
            , adjustWithKey
            , update
            , updateWithKey
            , updateLookupWithKey

            -- * Combine

            -- ** Union
            , union         
            , unionWith          
            , unionWithKey
            , unions
            , unionsWith

            -- ** Difference
            , difference
            , differenceWith
            , differenceWithKey
            
            -- ** Intersection
            , intersection           
            , intersectionWith
            , intersectionWithKey

            -- * Traversal
            -- ** Map
            , map
            , mapWithKey
            , mapAccum
            , mapAccumWithKey
            , mapKeys
            , mapKeysWith
            , mapKeysMonotonic

            -- ** Fold
            , fold
            , foldWithKey

            -- * Conversion
            , elems
            , keys
            , assocs
            
            -- ** Lists
            , toList
            , fromList
            , fromListWith
            , fromListWithKey

            -- ** Ordered lists
            , toAscList
            , fromAscList
            , fromAscListWith
            , fromAscListWithKey
            , fromDistinctAscList

            -- * Filter 
            , filter
            , filterWithKey
            , partition
            , partitionWithKey

            , split         
            , splitLookup   

            -- * Submap
            , isSubmapOf, isSubmapOfBy
            , isProperSubmapOf, isProperSubmapOfBy

            -- * Indexed 
            , lookupIndex
            , findIndex
            , elemAt
            , updateAt
            , deleteAt

            -- * Min\/Max
            , findMin
            , findMax
            , deleteMin
            , deleteMax
            , deleteFindMin
            , deleteFindMax
            , updateMin
            , updateMax
            , updateMinWithKey
            , updateMaxWithKey
            
            -- * Debugging
            , showTree
            , showTreeWith
            , valid
            ) -}
            where

import qualified Common.Lib.Map as Map

data InjMap a b = InjMap (Map.Map a b) (Map.Map b a)

insert

transpose


