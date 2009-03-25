module Maude.Meta.HasLabels (
    HasLabels(..)
) where

import Maude.Meta.Qid
-- import Maude.Meta.Term
import Maude.Meta.Module

import qualified Data.Set as Set
import qualified Data.Map as Map
-- import qualified Common.Lib.Rel as Rel


class HasLabels a where
    getLabels :: a -> QidSet
    mapLabels :: QidMap -> a -> a


instance HasLabels Attr where
    getLabels attr = case attr of
        Label l -> Set.singleton l
        _       -> Set.empty
    mapLabels mp attr = case attr of
        Label l -> Label (mapToFunction mp l)
        _       -> attr


instance (HasLabels a) => HasLabels [a] where
    getLabels = Set.unions . map getLabels
    mapLabels = map . mapLabels

instance (HasLabels a, HasLabels b) => HasLabels (a, b) where
    getLabels (a, b) = Set.union (getLabels a) (getLabels b)
    mapLabels mp (a, b) = (mapLabels mp a, mapLabels mp b)

instance (HasLabels a, HasLabels b, HasLabels c) => HasLabels (a, b, c) where
    getLabels (a, b, c) = Set.union (getLabels a) (getLabels (b, c))
    mapLabels mp (a, b, c) = (mapLabels mp a, mapLabels mp b, mapLabels mp c)

instance (Ord a, HasLabels a) => HasLabels (Set.Set a) where
    getLabels = Set.fold (Set.union . getLabels) Set.empty
    mapLabels = Set.map . mapLabels


instance HasLabels OpDecl where
    getLabels = getLabels . op'attrs
    mapLabels mp op = op {
        op'attrs = mapLabels mp (op'attrs op)
    }


instance HasLabels MembAx where
    getLabels mb = case mb of
        Mb _ _ as    -> getLabels as
        Cmb _ _ _ as -> getLabels as
    mapLabels mp mb = case mb of
        Mb t s as    -> Mb t s (mapLabels mp as)
        Cmb t s c as -> Cmb t s c (mapLabels mp as)


instance HasLabels Equation where
    getLabels eq = case eq of
        Eq _ _ as    -> getLabels as
        Ceq _ _ _ as -> getLabels as
    mapLabels mp eq = case eq of
        Eq t1 t2 as    -> Eq t1 t2 (mapLabels mp as)
        Ceq t1 t2 c as -> Ceq t1 t2 c (mapLabels mp as)


instance HasLabels Rule where
    getLabels rl = case rl of
        Rl _ _ as    -> getLabels as
        Crl _ _ _ as -> getLabels as
    mapLabels mp rl = case rl of
        Rl t1 t2 as    -> Rl t1 t2 (mapLabels mp as)
        Crl t1 t2 c as -> Crl t1 t2 c (mapLabels mp as)


mapToFunction :: (Ord a) => Map.Map a a -> (a -> a)
mapToFunction mp name = Map.findWithDefault name name mp
