module Maude.Meta.AsSymbol (
    AsSymbol(..),
    asSymbolSet,
    mapAsSymbol,
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta.HasName
import Maude.Util

import Data.Maybe (fromJust)
import qualified Data.Set as Set


class AsSymbol a where
    asSymbol :: a -> Symbol
    asSymbol = fromJust . asSymbolMaybe
    asSymbolMaybe :: a -> Maybe Symbol
    asSymbolMaybe = Just . asSymbol

asSymbolSet :: (AsSymbol a) => a -> SymbolSet
asSymbolSet = maybe Set.empty Set.singleton . asSymbolMaybe

mapAsSymbol :: (AsSymbol a) => (Symbol -> a) -> SymbolMap -> a -> a
mapAsSymbol ctr mp item = let extract = ctr . mapAsFunction mp
    in maybe item extract $ asSymbolMaybe item


instance AsSymbol Symbol where
    asSymbol = id


instance AsSymbol Type where
    asSymbol typ = case typ of
        TypeSort sort -> asSymbol sort
        TypeKind kind -> asSymbol kind

instance AsSymbol Sort where
    asSymbol = Sort . getName

instance AsSymbol Kind where
    asSymbol = Kind . getName

instance AsSymbol LabelId where
    asSymbol = Labl . getName

instance AsSymbol OpId where
    asSymbol = OpWildcard . getName

instance AsSymbol StmntAttr where
    asSymbolMaybe attr = case attr of
        Label name -> Just $ Labl name
        _          -> Nothing

instance AsSymbol Operator where
    asSymbol (Op op dom cod _) = let
            op'  = getName op
            dom' = map asSymbol dom
            cod' = asSymbol cod
        in Operator op' dom' cod'


instance AsSymbol Term where
    asSymbolMaybe term = case term of
        Const _ _ -> Nothing
        Var _ _   -> Nothing
        Apply op ts tp -> let
                dom = map (asSymbol . termType) ts
                cod = asSymbol tp
            in Just $ Operator op dom cod
