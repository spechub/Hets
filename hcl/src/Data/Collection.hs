----------------------------------------------------------------------------
-- |
-- Module      :  Data.Collection
-- Copyright   :  (c) Simon Foster (2005)
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  Platform Independant
--
-- A class for general collections. As such, probably not generic enough.
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

module Data.Collection (Collection(..)) where

import qualified Data.List
import qualified Data.Map
import qualified Data.Set

class Collection c where
    size  :: c -> Int
    empty :: c

instance Collection [a] where
    size  = Data.List.length
    empty = []

instance Collection (Data.Map.Map k a) where
    size  = Data.Map.size
    empty = Data.Map.empty

instance Collection (Data.Set.Set a) where
    size  = Data.Set.size
    empty = Data.Set.empty

null, isEmpty :: Collection c => c -> Bool
isEmpty = (==) 0 . size
null = isEmpty
