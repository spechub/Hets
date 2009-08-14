module Maude.Meta.HasSorts (
    HasSorts(..)
) where

import Maude.AS_Maude

import Maude.Meta.HasName

import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set

import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel


-- TODO: Maybe this class should be named `HasTypes` instead?
class HasSorts a where
    getSorts :: a -> Set Qid
    mapSorts :: Map Qid Qid -> a -> a


instance (HasSorts a) => HasSorts [a] where
    getSorts = Set.unions . map getSorts
    mapSorts = map . mapSorts

instance (HasSorts a, HasSorts b) => HasSorts (a, b) where
    getSorts (a, b) = Set.union (getSorts a) (getSorts b)
    mapSorts mp (a, b) = (mapSorts mp a, mapSorts mp b)

instance (HasSorts a, HasSorts b, HasSorts c) => HasSorts (a, b, c) where
    getSorts (a, b, c) = Set.union (getSorts a) (getSorts (b, c))
    mapSorts mp (a, b, c) = (mapSorts mp a, mapSorts mp b, mapSorts mp c)

instance (Ord a, HasSorts a) => HasSorts (Set a) where
    getSorts = Set.fold (Set.union . getSorts) Set.empty
    mapSorts = Set.map . mapSorts

instance (Ord a, HasSorts a) => HasSorts (Rel a) where
    getSorts = getSorts . Rel.nodes
    mapSorts = Rel.map . mapSorts


instance HasSorts Qid where
    getSorts = Set.singleton . getName
    mapSorts = mapName


instance HasSorts Sort where
    getSorts = Set.singleton . getName
    mapSorts = mapName


instance HasSorts Kind where
    getSorts = Set.singleton . getName
    mapSorts = mapName


instance HasSorts Type where
    getSorts typ = case typ of
        TypeSort sort -> getSorts sort
        TypeKind kind -> getSorts kind
    mapSorts mp typ = case typ of
        TypeSort sort -> TypeSort $ mapSorts mp sort
        TypeKind kind -> TypeKind $ mapSorts mp kind


instance HasSorts Operator where
    getSorts (Op _ dom cod _) = getSorts (dom, cod)
    mapSorts mp (Op op dom cod as) = Op op (mapSorts mp dom) (mapSorts mp cod) as


instance HasSorts Term where
    getSorts term = case term of
        Const _ t  -> getSorts t
        Var _ t    -> getSorts t
        Apply _ ts _ -> getSorts ts
    mapSorts mp term = case term of
        Const c t  -> Const c (mapSorts mp t)
        Var v t    -> Var v (mapSorts mp t)
        Apply t ts ty -> Apply t (mapSorts mp ts) ty


instance HasSorts Condition where
    getSorts cond = case cond of
        EqCond t1 t2    -> getSorts (t1, t2)
        MbCond t s      -> getSorts (t, s)
        MatchCond t1 t2 -> getSorts (t1, t2)
        RwCond t1 t2    -> getSorts (t1, t2)
    mapSorts mp cond = case cond of
        EqCond t1 t2    -> EqCond (mapSorts mp t1) (mapSorts mp t2)
        MbCond t s      -> MbCond (mapSorts mp t) (mapSorts mp s)
        MatchCond t1 t2 -> MatchCond (mapSorts mp t1) (mapSorts mp t2)
        RwCond t1 t2    -> RwCond (mapSorts mp t1) (mapSorts mp t2)


instance HasSorts Equation where
    getSorts (Eq t1 t2 cs _) = getSorts (t1, t2, cs)
    mapSorts mp (Eq t1 t2 cs as) = Eq (mapSorts mp t1) (mapSorts mp t2) (mapSorts mp cs) as


instance HasSorts Membership where
    getSorts (Mb ts ss cs _) = getSorts (ts, ss, cs)
    mapSorts mp (Mb ts ss cs as) = Mb (mapSorts mp ts) (mapSorts mp ss) (mapSorts mp cs) as


instance HasSorts Rule where
    getSorts (Rl t1 t2 cs _) = getSorts (t1, t2, cs)
    mapSorts mp (Rl t1 t2 cs as) = Rl (mapSorts mp t1) (mapSorts mp t2) (mapSorts mp cs) as
