{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A Generic XML Serializer using HXT and the Generics package (SYB3). This new version of
-- GXS is based on type classes, and thus allows modular customization. More coming soon.
--
-- This is a working serialize shell, with a number of default serialization rules imported.
-- As a result this module requires overlapping instances. If you don't want them, you need
-- to import Text.XML.Serializer.Core and write your own rules.
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
module Text.XML.Serializer ( module Text.XML.Serializer.Core
                           , module Text.XML.Serializer.Datatypes
                           , module Text.XML.Serializer.Derive
                           , module Text.XML.Serializer.Encoders
                           ) where

import Text.XML.Serializer.Core
import Text.XML.Serializer.Datatypes
import Text.XML.Serializer.DefaultRules
import Text.XML.Serializer.Derive
import Text.XML.Serializer.Encoders
