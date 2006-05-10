{-# OPTIONS_GHC -fglasgow-exts #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Data.AbstractMap
-- Copyright   :  (c) Simon Foster (2005)
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  Platform Independant
--
-- A class for collections which map keys to values.
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
module Data.AbstractMap where

import Prelude hiding (lookup)

import Data.Collection
import Data.Maybe
import qualified Data.List
import qualified Data.Map


class AbstractMap c k a | c -> k a where
    lookup      :: Monad m => k -> c -> m a
    keys        :: c -> [k]
    put         :: k -> a -> c -> c

class MapToList c k a | c -> k a where
    mapFromList :: [(k, a)] -> c
    mapToList   :: c -> [(k, a)] 

unsafeLookup :: AbstractMap c k a => k -> c -> a
unsafeLookup k c = fromJust $ lookup k c

instance Eq k => AbstractMap [(k, a)] k a where
    lookup  k c = maybe (fail "Data.AbstractMap.lookup: No association for given key") return $ Data.List.lookup k c
    keys    = Data.List.map fst
    put k a = ((k,a):)

instance Eq k => MapToList [(k, a)] k a where
    mapFromList = id
    mapToList   = id

instance Ord k => AbstractMap (Data.Map.Map k a) k a where
    lookup      = Data.Map.lookup
    keys        = Data.Map.keys
    put         = Data.Map.insert

instance Ord k => MapToList (Data.Map.Map k a) k a where
    mapToList   = Data.Map.toList
    mapFromList = Data.Map.fromList

mapFromListDefault :: (Collection c, AbstractMap c k v) => [(k, v)] -> c
mapFromListDefault ((k, v):m) =  put k v $ mapFromListDefault m
mapFromListDefault [] = empty

