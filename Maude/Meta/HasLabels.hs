module Maude.Meta.HasLabels (
    HasLabels(..)
) where

import Maude.AS_Maude
import Maude.Symbol

import Maude.Meta.HasName

import Data.Set (Set)
import qualified Data.Set as Set


class HasLabels a where
    getLabels :: a -> SymbolSet
    mapLabels :: SymbolMap -> a -> a


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
    getLabels attr = case attr of
        Label name -> getName name
        _          -> Set.empty
    mapLabels mp attr = case attr of
        Label name -> Label $ mapName mp name
        _          -> attr


instance HasLabels Equation where
    getLabels (Eq _ _ _ as) = getLabels as
    mapLabels mp (Eq t1 t2 cs as) = Eq t1 t2 cs (mapLabels mp as)


instance HasLabels Membership where
    getLabels (Mb _ _ _ as) = getLabels as
    mapLabels mp (Mb ts ss cs as) = Mb ts ss cs (mapLabels mp as)


instance HasLabels Rule where
    getLabels (Rl _ _ _ as) = getLabels as
    mapLabels mp (Rl t1 t2 cs as) = Rl t1 t2 cs (mapLabels mp as)
