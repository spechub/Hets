{-# OPTIONS -fglasgow-exts #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Data.DynamicMap
-- Copyright   :  (c) Simon Foster 2005
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- The Dynamic Map data-type is based on Finite Map and allows users to store any Typeable
-- data, in a strongly typed manner because the expected type of the value stored is
-- encapsulated in each key.
--
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
module Data.DynamicMap (DynamicMap, 
			lookupDM,
			lookupWithDefaultDM,
			lookupDM_D, 
			addToDM, 
			delFromDM, 
			isEmptyDM, 
			emptyDM, 
			DynamicKey,
			newDynamicKey,
		        unionDM
                        ) where

import qualified Data.Map
import Data.Dynamic
import Data.Maybe

data Typeable a => DynamicKey a = DK String a

-- | Create a new Dynamic Key, which associates a String and Type
newDynamicKey :: Typeable a => String -> a -> DynamicKey a
newDynamicKey = DK

type DynamicMap = Data.Map.Map String Dynamic

lookupDM :: Typeable a => DynamicKey a -> DynamicMap -> Maybe a
lookupDM (DK k _) m = Data.Map.lookup k m >>= fromDynamic

lookupWithDefaultDM :: Typeable a => DynamicKey a -> DynamicMap -> a
lookupWithDefaultDM k@(DK _ d) = fromMaybe d . lookupDM k

lookupDM_D :: Typeable a => DynamicKey a -> DynamicMap -> a
lookupDM_D = lookupWithDefaultDM

addToDM :: Typeable a => a -> DynamicKey a -> DynamicMap -> DynamicMap
addToDM x (DK k _) m = Data.Map.insert k (toDyn x) m

delFromDM :: Typeable a => DynamicKey a -> DynamicMap -> DynamicMap
delFromDM (DK k _) m = Data.Map.delete k m

isEmptyDM :: DynamicMap -> Bool
isEmptyDM m = Data.Map.null m

emptyDM :: DynamicMap
emptyDM = Data.Map.empty

unionDM :: DynamicMap -> DynamicMap -> DynamicMap
unionDM = Data.Map.union

