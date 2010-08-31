{- |
Module      :  $Header$
Description :  Accessing the Labels of Maude data types
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Accessing the Labels of Maude data types.

Defines a type class 'HasLabels' that lets us access the 'Label's of
Maude data types as 'SymbolSet's.

Consider importing "Maude.Meta" instead of this module.
-}

module Maude.Meta.HasLabels (
    -- * The HasLabels type class
    HasLabels(..)
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta.AsSymbol
import Maude.Meta.HasName

import Data.Set (Set)
import qualified Data.Set as Set

-- * The HasLabels  type class

-- | Represents something that contains a 'Set' of 'Label's (as 'Symbol's).
class HasLabels a where
    -- | Extract the 'Label's contained in the input.
    getLabels :: a -> SymbolSet
    -- | Map the 'Label's contained in the input.
    mapLabels :: SymbolMap -> a -> a

-- * Predefined instances

instance (HasLabels a) => HasLabels [a] where
    getLabels = Set.unions . map getLabels
    mapLabels = map . mapLabels

instance (HasLabels a, HasLabels b) => HasLabels (a, b) where
    getLabels (a, b) = Set.union (getLabels a) (getLabels b)
    mapLabels mp (a, b) = (mapLabels mp a, mapLabels mp b)

instance (HasLabels a, HasLabels b, HasLabels c) => HasLabels (a, b, c) where
    getLabels (a, b, c) = Set.union (getLabels a) (getLabels (b, c))
    mapLabels mp (a, b, c) = (mapLabels mp a, mapLabels mp b, mapLabels mp c)

instance (Ord a, HasLabels a) => HasLabels (Set a) where
    getLabels = Set.fold (Set.union . getLabels) Set.empty
    mapLabels = Set.map . mapLabels

instance HasLabels StmntAttr where
    getLabels = asSymbolSet
    mapLabels = mapAsSymbol $ Label . getName

instance HasLabels Membership where
    getLabels (Mb _ _ _ as) = getLabels as
    mapLabels mp (Mb ts ss cs as) = Mb ts ss cs (mapLabels mp as)

instance HasLabels Equation where
    getLabels (Eq _ _ _ as) = getLabels as
    mapLabels mp (Eq t1 t2 cs as) = Eq t1 t2 cs (mapLabels mp as)

instance HasLabels Rule where
    getLabels (Rl _ _ _ as) = getLabels as
    mapLabels mp (Rl t1 t2 cs as) = Rl t1 t2 cs (mapLabels mp as)
