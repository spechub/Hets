{-# OPTIONS -fglasgow-exts #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer.DefaultRules
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A set of default rules fo serialization, here so that overlapping instances can be avoided if 
-- necessary by writing your own rule set for every single data-type.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the 
-- GNU General Public License as published by the Free Software Foundation; either version 2 
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without 
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not, 
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Text.XML.Serializer.DefaultRules where

import Text.XML.Serializer.Core
import Text.XML.Serializer.Datatypes
import Text.XML.HXT.Parser
import Control.Monad.State
import Data.Generics2
import Data.Maybe
        
-- Default rule for namespaces.
--instance XMLNamespace a

instance XMLNamespace UpperBound

