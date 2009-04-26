module Maude.Meta.HasOps (
    HasOps(..)
) where

import Maude.Meta.Qid
import Maude.Meta.Term
import Maude.Meta.Module

import Data.Set (Set)
import qualified Data.Set as Set


class HasOps a where
    getOps :: a -> QidSet
    mapOps :: QidMap -> a -> a


instance HasOps Term where
    getOps term = case term of
        Term op ts -> Set.insert op (getOps ts)
        _          -> Set.empty
    mapOps mp term = case term of
        Term op ts -> Term (mapAsFunction mp op) (mapOps mp ts)
        _          -> term


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


instance HasOps OpDecl where
    getOps = Set.singleton . op'name
    mapOps mp op = op {
        op'name = mapAsFunction mp (op'name op)
    }


instance HasOps Condition where
    getOps cond = case cond of
        Nil               -> Set.empty
        Equal t1 t2       -> getOps (t1, t2)
        Member t _        -> getOps t
        Match t1 t2       -> getOps (t1, t2)
        Implies t1 t2     -> getOps (t1, t2)
        Conjunction c1 c2 -> getOps (c1, c2)
    mapOps mp cond = case cond of
        Nil               -> Nil
        Equal t1 t2       -> Equal (mapOps mp t1) (mapOps mp t2)
        Member t s        -> Member (mapOps mp t) s
        Match t1 t2       -> Match (mapOps mp t1) (mapOps mp t2)
        Implies t1 t2     -> Implies (mapOps mp t1) (mapOps mp t2)
        Conjunction c1 c2 -> Conjunction (mapOps mp c1) (mapOps mp c2)


instance HasOps MembAx where
    getOps mb = case mb of
        Mb t _ _    -> getOps t
        Cmb t _ c _ -> getOps (t, c)
    mapOps mp mb = case mb of
        Mb t s as    -> Mb (mapOps mp t) s as
        Cmb t s c as -> Cmb (mapOps mp t) s (mapOps mp c) as


instance HasOps Equation where
    getOps eq = case eq of
        Eq t1 t2 _    -> getOps (t1, t2)
        Ceq t1 t2 c _ -> getOps (t1, t2, c)
    mapOps mp eq = case eq of
        Eq t1 t2 as    -> Eq (mapOps mp t1) (mapOps mp t2) as
        Ceq t1 t2 c as -> Ceq (mapOps mp t1) (mapOps mp t2) (mapOps mp c) as


instance HasOps Rule where
    getOps rl = case rl of
        Rl t1 t2 _    -> getOps (t1, t2)
        Crl t1 t2 c _ -> getOps (t1, t2, c)
    mapOps mp rl = case rl of
        Rl t1 t2 as    -> Rl (mapOps mp t1) (mapOps mp t2) as
        Crl t1 t2 c as -> Crl (mapOps mp t1) (mapOps mp t2) (mapOps mp c) as
