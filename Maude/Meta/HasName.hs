module Maude.Meta.HasName (
    HasName(..)
) where

import Maude.AS_Maude

import Data.Map (Map)
import qualified Data.Map as Map


class HasName a where
    getName :: a -> Qid
    mapName :: Map Qid Qid -> a -> a


instance HasName Qid where
    getName = id
    mapName = map2Function

instance HasName Type where
    getName typ = case typ of
        TypeSort sort -> getName sort
        TypeKind kind -> getName kind
    mapName mp typ = case typ of
        TypeSort sort -> TypeSort $ mapName mp sort
        TypeKind kind -> TypeKind $ mapName mp kind

instance HasName Sort where
    getName (SortId name) = name
    mapName mp (SortId name) = SortId $ map2Function mp name

instance HasName Kind where
    getName (KindId name) = name
    mapName mp (KindId name) = KindId $ map2Function mp name

instance HasName ParamId where
    getName (ParamId name) = name
    mapName mp (ParamId name) = ParamId $ map2Function mp name

instance HasName ModId where
    getName (ModId name) = name
    mapName mp (ModId name) = ModId $ map2Function mp name

instance HasName ViewId where
    getName (ViewId name) = name
    mapName mp (ViewId name) = ViewId $ map2Function mp name

instance HasName LabelId where
    getName (LabelId name) = name
    mapName mp (LabelId name) = LabelId $ map2Function mp name

instance HasName OpId where
    getName (OpId name) = name
    mapName mp (OpId name) = OpId $ map2Function mp name

instance HasName Operator where
    getName (Op name _ _ _) = getName name
    mapName mp (Op name dom cod as) = Op (mapName mp name) dom cod as

instance HasName Module where
    getName (Module name _ _) = getName name
    mapName mp (Module name ps ss) = Module (mapName mp name) ps ss

instance HasName View where
    getName (View name _ _ _) = getName name
    mapName mp (View name from to rnms) = View (mapName mp name) from to rnms

instance HasName Spec where
    getName (SpecMod sp_module) = getName sp_module
    getName (SpecTh sp_th) = getName sp_th
    getName (SpecView sp_view) = getName sp_view
    mapName mp (SpecMod sp_module) = SpecMod $ mapName mp sp_module
    mapName mp (SpecTh sp_th) = SpecTh $ mapName mp sp_th
    mapName mp (SpecView sp_view) = SpecView $ mapName mp sp_view

map2Function :: (Ord a) => Map a a -> (a -> a)
map2Function mp name = Map.findWithDefault name name mp
