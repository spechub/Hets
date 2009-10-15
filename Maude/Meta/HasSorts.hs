{- |
Module      :  $Header$
Description :  Accessing the Sorts of Maude data types
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Accessing the Sorts of Maude data types.

Defines a type class 'HasSorts' that lets us access the 'Sort's of Maude
data types as 'SymbolSet's.

Consider importing "Maude.Meta" instead of this module.
-}

module Maude.Meta.HasSorts (
    -- * The HasSorts type class
    HasSorts(..)
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta.AsSymbol
import Maude.Meta.HasName

import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel

-- * The HasSorts type class

-- | Represents something that contains a 'Set' of 'Sort's (as 'Symbol's).
class HasSorts a where
    -- | Extract the 'Sort's contained in the input.
    getSorts :: a -> SymbolSet
    -- | Map the 'Sort's contained in the input.
    mapSorts :: SymbolMap -> a -> a

-- * Predefined instances

instance HasSorts Symbol where
    getSorts sym = case sym of
        Sort _ -> Set.singleton sym
        Kind _ -> Set.singleton $ asSort sym
        Operator _ dom cod -> getSorts(dom, cod)
        OpWildcard _ -> Set.empty
        Labl _ -> Set.empty
    mapSorts mp sym = case sym of
        Sort _ -> mapAsSymbol id mp sym
        Kind _ -> mapAsSymbol asKind mp $ asSort sym
        Operator qid dom cod -> let
                dom' = mapSorts mp dom
                cod' = mapSorts mp cod
            in Operator qid dom' cod'
        OpWildcard _ -> sym
        Labl _ -> sym

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

instance (Ord a, HasSorts a) => HasSorts (Map k a) where
    getSorts = Map.fold (Set.union . getSorts) Set.empty
    mapSorts = Map.map . mapSorts

instance (Ord a, HasSorts a) => HasSorts (Rel a) where
    getSorts = getSorts . Rel.nodes
    mapSorts = Rel.map . mapSorts

instance HasSorts Sort where
    getSorts = asSymbolSet
    mapSorts = mapAsSymbol $ SortId . getName

instance HasSorts Kind where
    getSorts = asSymbolSet
    mapSorts = mapAsSymbol $ KindId . getName

instance HasSorts Type where
    getSorts typ = case typ of
        TypeSort sort -> getSorts sort
        TypeKind kind -> getSorts kind
    mapSorts mp typ = case typ of
        TypeSort sort -> TypeSort $ mapSorts mp sort
        TypeKind kind -> TypeKind $ mapSorts mp kind

instance HasSorts Operator where
    getSorts (Op _ dom cod _) = getSorts (dom, cod)
    mapSorts mp (Op op dom cod as) = let
            dom' = mapSorts mp dom
            cod' = mapSorts mp cod
        in Op op dom' cod' as

instance HasSorts Attr where
    getSorts attr = case attr of
        Id term      -> getSorts term
        LeftId term  -> getSorts term
        RightId term -> getSorts term
        _ -> Set.empty
    mapSorts mp attr = case attr of
        Id term      -> Id $ mapSorts mp term
        LeftId term  -> LeftId $ mapSorts mp term
        RightId term -> RightId $ mapSorts mp term
        _ -> attr

instance HasSorts Term where
    getSorts term = case term of
        Const _ tp    -> getSorts tp
        Var _ tp      -> getSorts tp
        Apply _ ts tp -> getSorts (ts, tp)
    mapSorts mp term = case term of
        Const con tp   -> Const con (mapSorts mp tp)
        Var var tp     -> Var var (mapSorts mp tp)
        Apply op ts tp -> Apply op (mapSorts mp ts) (mapSorts mp tp)

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

instance HasSorts Membership where
    getSorts (Mb t s cs _) = getSorts (t, s, cs)
    mapSorts mp (Mb t s cs as) = let
            t'  = mapSorts mp t
            s'  = mapSorts mp s
            cs' = mapSorts mp cs
        in Mb t' s' cs' as

instance HasSorts Equation where
    getSorts (Eq t1 t2 cs _) = getSorts (t1, t2, cs)
    mapSorts mp (Eq t1 t2 cs as) = let
            t1' = mapSorts mp t1
            t2' = mapSorts mp t2
            cs' = mapSorts mp cs
        in Eq t1' t2' cs' as

instance HasSorts Rule where
    getSorts (Rl t1 t2 cs _) = getSorts (t1, t2, cs)
    mapSorts mp (Rl t1 t2 cs as) = let
            t1' = mapSorts mp t1
            t2' = mapSorts mp t2
            cs' = mapSorts mp cs
        in Rl t1' t2' cs' as
