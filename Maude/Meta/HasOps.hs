module Maude.Meta.HasOps (
    HasOps(..)
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta.AsSymbol
import Maude.Meta.HasName

import Data.Set (Set)
import qualified Data.Set as Set


class HasOps a where
    getOps :: a -> SymbolSet
    mapOps :: SymbolMap -> a -> a


instance HasOps Symbol where
    getOps sym = case sym of
        Operator _ _ _ -> Set.singleton sym
        _ -> Set.empty
    mapOps mp sym = case sym of
        Operator _ _ _ -> mapAsSymbol id mp sym
        _ -> sym


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
    getOps = asSymbolSet
    mapOps mp op@(Op _ _ _ as) = let
            swapAttrs (Op qid dom cod _) = Op qid dom cod as
        in mapAsSymbol (swapAttrs . toOperator) mp op


instance HasOps Attr where
    getOps attr = case attr of
        Id term      -> getOps term
        LeftId term  -> getOps term
        RightId term -> getOps term
        _ -> Set.empty
    mapOps mp attr = case attr of
        Id term      -> Id $ mapOps mp term
        LeftId term  -> LeftId $ mapOps mp term
        RightId term -> RightId $ mapOps mp term
        _ -> attr


instance HasOps Term where
    getOps term = case term of
        Apply _ ts _ -> Set.insert (asSymbol term) (getOps ts)
        _ -> Set.empty
    mapOps mp term = case term of
        Apply _ ts tp -> let
                op = getName $ mapOps mp $ asSymbol term
            in Apply op (mapOps mp ts) tp
        _ -> term


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


instance HasOps Membership where
    getOps (Mb t _ cs _) = getOps (t, cs)
    mapOps mp (Mb t s cs as) = let
            t' = mapOps mp t
            cs' = mapOps mp cs
        in Mb t' s cs' as


instance HasOps Equation where
    getOps (Eq t1 t2 cs _) = getOps (t1, t2, cs)
    mapOps mp (Eq t1 t2 cs as) = let
            t1' = mapOps mp t1
            t2' = mapOps mp t2
            cs' = mapOps mp cs
        in Eq t1' t2' cs' as


instance HasOps Rule where
    getOps (Rl t1 t2 cs _) = getOps (t1, t2, cs)
    mapOps mp (Rl t1 t2 cs as) = let
            t1' = mapOps mp t1
            t2' = mapOps mp t2
            cs' = mapOps mp cs
        in Rl t1' t2' cs' as
