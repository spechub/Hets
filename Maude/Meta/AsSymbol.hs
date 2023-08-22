{- |
Module      :  ./Maude/Meta/AsSymbol.hs
Description :  Viewing Maude data types as Symbols
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Viewing Maude data types as Symbols.

Defines a type class 'AsSymbol' that lets us treat Maude data types as
'Symbol's, converting back and forth between them as needed.

Consider importing "Maude.Meta" instead of this module.
-}

module Maude.Meta.AsSymbol (
    -- * The AsSymbol type class
    AsSymbol (..),
    -- * Auxiliary functions
    asSymbolSet,
    mapAsSymbol,
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta.HasName
import Maude.Util

import Data.Maybe (fromJust)
import qualified Data.Set as Set

-- * The AsSymbol type class

{- | Represents something that can be converted into a 'Symbol'.
Instances should only override /one/ of its class methods: -}
--
{- * Use 'asSymbol' when every member of the instance type can be
represented as a 'Symbol'. -}
--
-- * Use 'asSymbolMaybe' otherwise.
--
-- Each function is defined in terms of the other one by default.

class AsSymbol a where
    -- | Convert the input into a 'Symbol'.
    asSymbol :: a -> Symbol
    asSymbol = fromJust . asSymbolMaybe
    -- | Convert the input into 'Maybe' a 'Symbol'
    asSymbolMaybe :: a -> Maybe Symbol
    asSymbolMaybe = Just . asSymbol

-- * Auxiliary functions

-- | Instead of a single 'Symbol', convert the input into a 'SymbolSet'.
asSymbolSet :: (AsSymbol a) => a -> SymbolSet
asSymbolSet = maybe Set.empty Set.singleton . asSymbolMaybe

{- | Apply a 'SymbolMap' to the input, then convert the result back to
the original type. -}
mapAsSymbol :: (AsSymbol a) => (Symbol -> a) -> SymbolMap -> a -> a
mapAsSymbol ctr mp item = let extract = ctr . mapAsFunction mp
    in maybe item extract $ asSymbolMaybe item

-- * Predefined 'AsSymbol' instances

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
        _ -> Nothing

instance AsSymbol Operator where
    asSymbol (Op op dom cod _) = let
            op' = getName op
            dom' = map asSymbol dom
            cod' = asSymbol cod
        in Operator op' dom' cod'

instance AsSymbol Term where
    asSymbolMaybe term = case term of
        Const _ _ -> Nothing
        Var _ _ -> Nothing
        Apply op ts tp -> let
                dom = map (asSymbol . getTermType) ts
                cod = asSymbol tp
            in Just $ Operator op dom cod
