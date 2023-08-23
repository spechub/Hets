{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  ./Maude/Meta/HasName.hs
Description :  Accessing the names of Maude data types
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Accessing the names of Maude data types.

Defines a type class 'HasName' that lets us access the names of Maude
data types as 'Qid's.

Consider importing "Maude.Meta" instead of this module.
-}

module Maude.Meta.HasName (
    -- * The HasName type class
    HasName (..)
) where

import Maude.AS_Maude

-- * The HasName type class

-- | Represents something that has a name (as a 'Qid').
class HasName a where
    -- | Extract the name of the input.
    getName :: a -> Qid
    -- | Map the name of the input.
    mapName :: (Qid -> Qid) -> a -> a

-- * Predefined instances

instance HasName Qid where
    getName = id
    mapName = id

instance HasName Type where
    getName typ = case typ of
        TypeSort sort -> getName sort
        TypeKind kind -> getName kind
    mapName mp typ = case typ of
        TypeSort sort -> TypeSort $ mapName mp sort
        TypeKind kind -> TypeKind $ mapName mp kind

instance HasName Sort where
    getName (SortId name) = name
    mapName mp (SortId name) = SortId $ mp name

instance HasName Kind where
    getName (KindId name) = name
    mapName mp (KindId name) = KindId $ mp name

instance HasName ParamId where
    getName (ParamId name) = name
    mapName mp (ParamId name) = ParamId $ mp name

instance HasName ModId where
    getName (ModId name) = name
    mapName mp (ModId name) = ModId $ mp name

instance HasName ViewId where
    getName (ViewId name) = name
    mapName mp (ViewId name) = ViewId $ mp name

instance HasName LabelId where
    getName (LabelId name) = name
    mapName mp (LabelId name) = LabelId $ mp name

instance HasName OpId where
    getName (OpId name) = name
    mapName mp (OpId name) = OpId $ mp name

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
    getName spec = case spec of
        SpecMod modul -> getName modul
        SpecTh theory -> getName theory
        SpecView view -> getName view
    mapName mp spec = case spec of
        SpecMod modul -> SpecMod $ mapName mp modul
        SpecTh theory -> SpecTh $ mapName mp theory
        SpecView view -> SpecView $ mapName mp view
