module Maude.Meta.HasName (
    HasName(..)
) where

import Maude.AS_Maude
import Maude.Symbol

import Data.Map (Map)
import qualified Data.Map as Map


class HasName a where
    getName :: a -> Symbol
    mapName :: SymbolMap -> a -> a


instance HasName Symbol where
    getName = id
    mapName = mapAsFunction

instance HasName Type where
    getName typ = case typ of
        TypeSort sort -> getName sort
        TypeKind kind -> getName kind
    mapName mp typ = case typ of
        TypeSort sort -> TypeSort $ mapName mp sort
        TypeKind kind -> TypeKind $ mapName mp kind

instance HasName Sort where
    getName (SortId name) = name
    mapName mp (SortId name) = SortId $ mapAsFunction mp name

instance HasName Kind where
    getName (KindId name) = name
    mapName mp (KindId name) = KindId $ mapAsFunction mp name

instance HasName ParamId where
    getName (ParamId name) = name
    mapName mp (ParamId name) = ParamId $ mapAsFunction mp name

instance HasName ModId where
    getName (ModId name) = name
    mapName mp (ModId name) = ModId $ mapAsFunction mp name

instance HasName LabelId where
    getName (LabelId name) = name
    mapName mp (LabelId name) = LabelId $ mapAsFunction mp name

instance HasName OpId where
    getName (OpId name) = name
    mapName mp (OpId name) = OpId $ mapAsFunction mp name

instance HasName Operator where
    getName (Op name _ _ _) = getName name
    mapName mp (Op name dom cod as) = Op (mapName mp name) dom cod as

instance HasName Spec where
    getName (Spec name _ _) = getName name
    mapName mp (Spec name ps ss) = Spec (mapName mp name) ps ss

instance HasName Theory where
    getName (Theory name _) = getName name
    mapName mp (Theory name ss) = Theory (mapName mp name) ss


mapAsFunction :: (Ord a) => Map a a -> (a -> a)
mapAsFunction mp name = Map.findWithDefault name name mp
