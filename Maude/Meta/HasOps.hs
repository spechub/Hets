module Maude.Meta.HasOps (
    HasOps(..)
) where

import Maude.AS_Maude

import Maude.Meta.HasName

import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set


class HasOps a where
    getOps :: a -> Set Qid
    mapOps :: Map Qid Qid -> a -> a


instance (HasOps a) => HasOps [a] where
    getOps = Set.unions . map getOps
    mapOps = map . mapOps

instance (HasOps a, HasOps b) => HasOps (a, b) where
    getOps (a, b) = Set.union (getOps a) (getOps b)
    mapOps mp (a, b) = (mapOps mp a, mapOps mp b)

instance (HasOps a, HasOps b, HasOps c) => HasOps (a, b, c) where
    getOps (a, b, c) = Set.union (getOps a) (getOps (b, c))
    mapOps mp (a, b, c) = (mapOps mp a, mapOps mp b, mapOps mp c)

instance (Ord a, HasOps a) => HasOps (Set a) where
    getOps = Set.fold (Set.union . getOps) Set.empty
    mapOps = Set.map . mapOps


instance HasOps Operator where
    getOps = Set.singleton . getName
    mapOps = mapName


instance HasOps Term where
    getOps term = case term of
        Apply op ts _ -> Set.insert (getName op) (getOps ts)
        _           -> Set.empty
    mapOps mp term = case term of
        Apply op ts ty -> Apply (mapName mp op) (mapOps mp ts) ty
        _           -> term


instance HasOps Condition where
    getOps cond = case cond of
        EqCond t1 t2    -> getOps (t1, t2)
        MbCond t _      -> getOps t
        MatchCond t1 t2 -> getOps (t1, t2)
        RwCond t1 t2    -> getOps (t1, t2)
    mapOps mp cond = case cond of
        EqCond t1 t2    -> EqCond (mapOps mp t1) (mapOps mp t2)
        MbCond t s      -> MbCond (mapOps mp t) s
        MatchCond t1 t2 -> MatchCond (mapOps mp t1) (mapOps mp t2)
        RwCond t1 t2    -> RwCond (mapOps mp t1) (mapOps mp t2)


instance HasOps Equation where
    getOps (Eq t1 t2 cs _) = getOps (t1, t2, cs)
    mapOps mp (Eq t1 t2 cs as) = Eq (mapOps mp t1) (mapOps mp t2) (mapOps mp cs) as


instance HasOps Membership where
    getOps (Mb ts _ cs _) = getOps (ts, cs)
    mapOps mp (Mb ts ss cs as) = Mb (mapOps mp ts) ss (mapOps mp cs) as


instance HasOps Rule where
    getOps (Rl t1 t2 cs _) = getOps (t1, t2, cs)
    mapOps mp (Rl t1 t2 cs as) = Rl (mapOps mp t1) (mapOps mp t2) (mapOps mp cs) as
