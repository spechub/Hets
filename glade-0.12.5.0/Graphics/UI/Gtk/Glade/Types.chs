{-# LANGUAGE CPP #-}
{-# OPTIONS_HADDOCK hide #-}
-- -*-haskell-*-
-- -------------------- automatically generated file - do not edit ----------
--  Object hierarchy for the GIMP Toolkit (GTK) Binding for Haskell
--
--  Author : Axel Simon
--
--  Copyright (C) 2001-2005 Axel Simon
--
--  This library is free software; you can redistribute it and/or
--  modify it under the terms of the GNU Lesser General Public
--  License as published by the Free Software Foundation; either
--  version 2.1 of the License, or (at your option) any later version.
--
--  This library is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  Lesser General Public License for more details.
--
-- #hide

-- |
-- Maintainer  : gtk2hs-users@lists.sourceforge.net
-- Stability   : provisional
-- Portability : portable (depends on GHC)
--
-- This file reflects the Gtk+ object hierarchy in terms of Haskell classes.
--
-- Note: the mk... functions were originally meant to simply be an alias
-- for the constructor. However, in order to communicate the destructor
-- of an object to objectNew, the mk... functions are now a tuple containing
-- Haskell constructor and the destructor function pointer. This hack avoids
-- changing all modules that simply pass mk... to objectNew.
--
module Graphics.UI.Gtk.Glade.Types (

  module Graphics.UI.GtkInternals,
  GladeXML(GladeXML), GladeXMLClass,
  toGladeXML, 
  mkGladeXML, unGladeXML,
  castToGladeXML, gTypeGladeXML
  ) where

import Foreign.ForeignPtr (ForeignPtr, castForeignPtr)
#if __GLASGOW_HASKELL__ >= 707
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
#else
import Foreign.ForeignPtr (unsafeForeignPtrToPtr)
#endif
import Foreign.C.Types    (CULong(..), CUInt(..))
import System.Glib.GType  (GType, typeInstanceIsA)
{#import Graphics.UI.GtkInternals#}

{# context lib="gtk" prefix="gtk" #}

-- The usage of foreignPtrToPtr should be safe as the evaluation will only be
-- forced if the object is used afterwards
--
castTo :: (GObjectClass obj, GObjectClass obj') => GType -> String
                                                -> (obj -> obj')
castTo gtype objTypeName obj =
  case toGObject obj of
    gobj@(GObject objFPtr)
      | typeInstanceIsA ((unsafeForeignPtrToPtr.castForeignPtr) objFPtr) gtype
                  -> unsafeCastGObject gobj
      | otherwise -> error $ "Cannot cast object to " ++ objTypeName


-- ******************************************************************* GladeXML

{#pointer *GladeXML as GladeXML foreign newtype #} deriving (Eq,Ord)

mkGladeXML = (GladeXML, objectUnrefFromMainloop)
unGladeXML (GladeXML o) = o

class GObjectClass o => GladeXMLClass o
toGladeXML :: GladeXMLClass o => o -> GladeXML
toGladeXML = unsafeCastGObject . toGObject

instance GladeXMLClass GladeXML
instance GObjectClass GladeXML where
  toGObject = GObject . castForeignPtr . unGladeXML
  unsafeCastGObject = GladeXML . castForeignPtr . unGObject

castToGladeXML :: GObjectClass obj => obj -> GladeXML
castToGladeXML = castTo gTypeGladeXML "GladeXML"

gTypeGladeXML :: GType
gTypeGladeXML =
  {# call fun unsafe glade_xml_get_type #}

