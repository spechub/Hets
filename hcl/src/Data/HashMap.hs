{-# OPTIONS_GHC -fglasgow-exts #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Data.HashMap
-- Copyright   :  (c) Simon Foster (2005)
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  Platform Independant
--
-- An inefficient, incomplete implementation of HashMaps. Feel free to hack.
-- This implementation has been translated verbatim from the GNU Classpath version.
-- See <http://www.gnu.org/software/classpath/>
----------------------------------------------------------------------------
-- @This file is part of HCl.@
--
-- @HCl is free software; you can redistribute it and\/or modify it under the terms of the 
-- GNU General Public License as published by the Free Software Foundation; either version 2 
-- of the License, or (at your option) any later version.@
--
-- @HCl is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without 
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HCl; if not, 
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Data.HashMap where

import Data.Maybe
import Data.Array
import Data.List
import Data.Int
import Data.Char

import Data.Collection
import Data.AbstractMap
import Data.HashTable (hashInt, hashString)

instance Hashable k => Collection (HashMap k v) where
    size  = hm_size
    empty = emptyHashMap

instance (Eq k) => AbstractMap (HashMap k v) k v where
    lookup      = lookupHashMap
    keys        = keysHashMap
    put         = insertHashMap

instance (Eq k, Hashable k) => MapToList (HashMap k v) k v where
    mapFromList = mapFromListDefault
    mapToList   = toListHashMap

class Hashable a where
    hash :: a -> Int32

instance Hashable Int32 where
    hash n = n `mod` 1500007

instance Hashable String where
    hash = fromIntegral . foldr f 0
      where f c m = ord c + (m * 128) `rem` 1500007

data HashMap k v = HashMap { loadFactor :: Float
                           , buckets    :: Array Int32 (Maybe (k, v))
                           , hasher     :: k -> Int32
                           , hm_size    :: Int -- For efficiency
                           }

threshold :: HashMap k v -> Int32
threshold m = round $ (loadFactor m) * (fromIntegral $ snd $ bounds $ buckets m)

toListHashMap :: HashMap k v -> [(k, v)]
toListHashMap = catMaybes . elems . buckets

-- FIXME: The following three functions are inefficient.
sizeHashMap = length . toListHashMap
keysHashMap  = map fst . toListHashMap
elemsHashMap = map snd . toListHashMap

instance (Show k, Show v) => Show (HashMap k v) where
    show x = "{" ++ (concat $ intersperse ", " $ map (\(k,v) -> show k ++ ":=" ++ show v) $ toListHashMap x) ++ "}"

defaultLoadFactor :: Float
defaultLoadFactor = 0.75

defaultSize :: Int32
defaultSize = 11

emptyHashMap :: Hashable k => HashMap k v
emptyHashMap = emptyHashMapN defaultLoadFactor defaultSize hash

emptyHashMapN :: Float -> Int32 -> (k -> Int32) -> HashMap k v
emptyHashMapN l n h = HashMap { loadFactor = l
                              , buckets = listArray (0, n - 1) (repeat Nothing) 
                              , hasher = h 
                              , hm_size = 0 }

hashRelative :: k -> HashMap k v -> Int32
hashRelative x m = (hasher m) x `mod` ((\(a,b) -> b - a) $ bounds $ buckets m)


insertHashMap :: k -> v -> HashMap k v -> HashMap k v
insertHashMap k v m = let h = indx $ hashRelative k m in
                              if (h > threshold m) then insertHashMap k v (rehash m)
                                                   else m { buckets = (buckets m) // [(h, Just (k, v))] 
                                                          , hm_size = (hm_size m) + 1 
                                                          }
   where indx n = if (n > (snd $ bounds $ buckets m)) 
                     then n
                     else (if (isJust $ (buckets m ! n)) then indx (n + 1) else n)

lookupHashMap :: (Eq k, Monad m) => k -> HashMap k v -> m v
lookupHashMap k m = indx (hashRelative k m)
    where indx n = case (buckets m ! n) of
                     Just (k', v) -> if (k' == k) then return v
                                                  else indx (n+1)
                     Nothing -> fail "lookupHashMap: No association for given key"

deleteHashMap :: Eq k => k -> HashMap k v -> HashMap k v
deleteHashMap k m = del (hashRelative k m)
    where del n = case (buckets m ! n) of
                    Just (k', v) -> if (k' == k) then m { buckets = buckets m // [(n, Nothing)] 
                                                        , hm_size = (hm_size m) - 1} 
                                                 else del (n+1)
                    Nothing -> m

rehash :: HashMap k v -> HashMap k v
rehash m = let l' = (((\(a,b) -> b - a) $ bounds $ buckets m) * 2) + 1 
               m' = emptyHashMapN defaultLoadFactor l' (hasher m) in
		  m' { buckets = (buckets m') // (map (\(k,v) -> (hashRelative k m', Just (k,v))) $ toListHashMap m) }
	       

