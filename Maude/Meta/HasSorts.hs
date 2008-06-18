module Maude.Meta.HasSorts (
    HasSorts(..)
) where

import Maude.Meta.Qid
import Maude.Meta.Term
import Maude.Meta.Module

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel


class HasSorts a where
    getSorts :: a -> SortSet
    mapSorts :: QidMap -> a -> a


instance HasSorts Sort where
    getSorts = Set.singleton
    mapSorts = mapToFunction


instance (HasSorts a) => HasSorts [a] where
    getSorts = Set.unions . map getSorts
    mapSorts = map . mapSorts

instance (HasSorts a, HasSorts b) => HasSorts (a, b) where
    getSorts (a, b) = Set.union (getSorts a) (getSorts b)
    mapSorts mp (a, b) = (mapSorts mp a, mapSorts mp b)

instance (HasSorts a, HasSorts b, HasSorts c) => HasSorts (a, b, c) where
    getSorts (a, b, c) = Set.union (getSorts a) (getSorts (b, c))
    mapSorts mp (a, b, c) = (mapSorts mp a, mapSorts mp b, mapSorts mp c)

instance (Ord a, HasSorts a) => HasSorts (Set.Set a) where
    getSorts = Set.fold (Set.union . getSorts) Set.empty
    mapSorts = Set.map . mapSorts

instance (Ord a, HasSorts a) => HasSorts (Rel.Rel a) where
    getSorts = getSorts . Rel.nodes
    mapSorts = Rel.map . mapSorts


instance HasSorts Type where
    getSorts typ = case typ of
        Sort s  -> Set.singleton s
        Kind ss -> Set.fromList ss
    mapSorts mp typ = case typ of
        Sort s  -> Sort (mapSorts mp s)
        Kind ss -> Kind (mapSorts mp ss)


instance HasSorts Term where
    getSorts term = case term of
        Constant _ t -> getSorts t
        Variable _ t -> getSorts t
        Term _ ts    -> getSorts ts
    mapSorts mp term = case term of
        Constant c t -> Constant c (mapSorts mp t)
        Variable v t -> Variable v (mapSorts mp t)
        Term t ts    -> Term t (mapSorts mp ts)


instance HasSorts OpDecl where
    getSorts op = getSorts (op'domain op, op'range op)
    mapSorts mp op = op {
        op'domain = mapSorts mp (op'domain op),
        op'range = mapSorts mp (op'range op)
    }


instance HasSorts Condition where
    getSorts cond = case cond of
        Nil               -> Set.empty
        Equal t1 t2       -> getSorts (t1, t2)
        Member t s        -> getSorts (s, t)
        Match t1 t2       -> getSorts (t1, t2)
        Implies t1 t2     -> getSorts (t1, t2)
        Conjunction c1 c2 -> getSorts (c1, c2)
    mapSorts mp cond = case cond of
        Nil               -> Nil
        Equal t1 t2       -> Equal (mapSorts mp t1) (mapSorts mp t2)
        Member t s        -> Member (mapSorts mp t) (mapSorts mp s)
        Match t1 t2       -> Match (mapSorts mp t1) (mapSorts mp t2)
        Implies t1 t2     -> Implies (mapSorts mp t1) (mapSorts mp t2)
        Conjunction c1 c2 -> Conjunction (mapSorts mp c1) (mapSorts mp c2)


instance HasSorts MembAx where
    getSorts mb = case mb of
        Mb t s _    -> getSorts (s, t)
        Cmb t s c _ -> getSorts (s, t, c)
    mapSorts mp mb = case mb of
        Mb t s as    -> Mb (mapSorts mp t) (mapSorts mp s) as
        Cmb t s c as -> Cmb (mapSorts mp t) (mapSorts mp s) (mapSorts mp c) as


instance HasSorts Equation where
    getSorts eq = case eq of
        Eq t1 t2 _    -> getSorts (t1, t2)
        Ceq t1 t2 c _ -> getSorts (t1, t2, c)
    mapSorts mp eq = case eq of
        Eq t1 t2 as    -> Eq (mapSorts mp t1) (mapSorts mp t2) as
        Ceq t1 t2 c as -> Ceq (mapSorts mp t1) (mapSorts mp t2) (mapSorts mp c) as


instance HasSorts Rule where
    getSorts rl = case rl of
        Rl t1 t2 _    -> getSorts (t1, t2)
        Crl t1 t2 c _ -> getSorts (t1, t2, c)
    mapSorts mp rl = case rl of
        Rl t1 t2 as    -> Rl (mapSorts mp t1) (mapSorts mp t2) as
        Crl t1 t2 c as -> Crl (mapSorts mp t1) (mapSorts mp t2) (mapSorts mp c) as


mapToFunction :: (Ord a) => Map.Map a a -> (a -> a)
mapToFunction mp name = Map.findWithDefault name name mp