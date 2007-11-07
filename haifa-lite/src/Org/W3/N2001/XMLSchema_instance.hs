{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fth #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Org.W3.N2001.XMLSchema_instance
-- Copyright   :  (c) Simon Foster 2005
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  aca01sdf@shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- An equivelant module for <http://www.w3.org/2001/XMLSchema_instance> schema and the data-types therein.
-- This module provides an XSI Typing hook, which allow the type attribute to be encoded within XML
-- namespaces to indicate the XSD type of the data within an element. This module is very incomplete,
-- and a mess atm.
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
module Org.W3.N2001.XMLSchema_instance where

import Data.DynamicMap
import Org.W3.N2001.XMLSchema
import Text.XML.HXT.Parser
import Text.XML.Serializer.Datatypes
import Network.URI
import Data.Maybe

Just thisNamespace = parseURI "http://www.w3.org/2001/XMLSchema-instance"
thisPrefix = "xsi"
