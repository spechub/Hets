{- |
Module      :  $Header$
Description :  Maude Symbols
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for Maude.
-}

module Maude.Symbol (
    -- * Types
    -- ** The Symbol type
    Symbol(..),
    -- ** Auxiliary types
    Symbols,
    SymbolSet,
    SymbolMap,
    SymbolRel,
    -- * Conversion
    toId,
    qualify,
    asSort,
    asKind,
    toType,
    toOperator,
    -- * Construction
    mkOpTotal,
    mkOpPartial,
    -- * Testing
    sameKind,
) where


import Maude.AS_Maude
import Maude.Meta.HasName

import Data.Set (Set)
import Data.Map (Map)
import Common.Lib.Rel (Rel)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

import Common.Id (Id, mkId, mkSimpleId, GetRange, getRange, nullRange)
import Common.Doc
import Common.DocUtils (Pretty(..))

import Data.Maybe (fromJust)


-- | Represents a Sort, Kind, Label, or Operator.
data Symbol = Sort Qid                      -- ^ A Sort Symbol
            | Kind Qid                      -- ^ A Kind Symbol
            | Labl Qid                      -- ^ A Label Symbol
            | Operator Qid Symbols Symbol   -- ^ A qualified Operator Symbol
            | OpWildcard Qid                -- ^ A wildcard Operator Symbol
            deriving (Show, Read, Ord, Eq)
type Symbols   = [Symbol]
type SymbolSet = Set Symbol
type SymbolMap = Map Symbol Symbol
type SymbolRel = Rel Symbol


instance HasName Symbol where
    getName symb = case symb of
        Sort qid -> qid
        Kind qid -> qid
        Labl qid -> qid
        OpWildcard qid -> qid
        Operator qid _ _ -> qid
    mapName mp symb = case symb of
        Sort qid -> Sort $ mapName mp qid
        Kind qid -> Kind $ mapName mp qid
        Labl qid -> Labl $ mapName mp qid
        OpWildcard qid -> OpWildcard $ mapName mp qid
        Operator qid dom cod -> Operator (mapName mp qid) dom cod


instance Pretty Symbol where
    pretty symb = case symb of
        Sort qid -> pretty qid
        Kind qid -> brackets $ pretty qid
        Labl qid -> pretty qid
        OpWildcard qid -> pretty qid
        Operator qid dom cod -> hsep
            [pretty qid, colon, hsep $ map pretty dom, funArrow, pretty cod]


instance GetRange Symbol where
    getRange _ = nullRange


-- | Convert Symbol to Id.
toId :: Symbol -> Id
toId = mkId . return . getName

-- | Qualify the Symbol name with a Qid.
qualify :: Qid -> Symbol -> Symbol
qualify qid = let prepend sym = mkSimpleId $ concat [show qid, "$", show sym]
              in mapName $ prepend . getName

-- | Convert Symbol to Symbol, changing Kinds to Sorts.
asSort :: Symbol -> Symbol
asSort symb = case symb of
    Kind qid -> Sort qid
    _ -> symb

-- | Convert Symbol to Symbol, changing Sorts to Kinds.
asKind :: Symbol -> Symbol
asKind symb = case symb of
    Sort qid -> Kind qid
    _ -> symb


isType :: Symbol -> Bool
isType symb = case symb of
    Sort _ -> True
    Kind _ -> True
    _ -> False

toTypeMaybe :: Symbol -> Maybe Type
toTypeMaybe symb = case symb of
    Sort qid -> Just . TypeSort . SortId $ qid
    Kind qid -> Just . TypeKind . KindId $ qid
    _ -> Nothing

-- | Convert Symbol to Type, if possible.
toType :: Symbol -> Type
toType = fromJust . toTypeMaybe


isOpWildcard :: Symbol -> Bool
isOpWildcard symb = case symb of
    OpWildcard _ -> True
    _ -> False

isOperator :: Symbol -> Bool
isOperator symb = case symb of
    Operator _ _ _ -> True
    _ -> False

toOperatorMaybe :: Symbol -> Maybe Operator
toOperatorMaybe symb = case symb of
    Operator qid dom cod -> Just $
        Op (OpId qid) (map toType dom) (toType cod) []
    _ -> Nothing

-- | Convert Symbol to Operator, if possible.
toOperator :: Symbol -> Operator
toOperator = fromJust . toOperatorMaybe


-- | Create a total operator Symbol with the given profile.
mkOpTotal :: Qid -> [Qid] -> Qid -> Symbol
mkOpTotal qid dom cod = Operator qid (map Sort dom) (Sort cod)

-- | Create a partial operator Symbol with the given profile.
mkOpPartial :: Qid -> [Qid] -> Qid -> Symbol
mkOpPartial qid dom cod = Operator qid (map Sort dom) (Kind cod)


typeSameKind :: SymbolRel -> Symbol -> Symbol -> Bool
typeSameKind rel s1 s2 = let
    preds1 = Rel.predecessors rel s1
    preds2 = Rel.predecessors rel s2
    succs1 = Rel.succs rel s1
    succs2 = Rel.succs rel s2
    psect  = Set.intersection preds1 preds2
    ssect  = Set.intersection succs1 succs2
    in any id [ s1 == s2
              , Set.member s2 preds1
              , Set.member s1 preds2
              , Set.member s2 succs1
              , Set.member s1 succs2
              , not $ Set.null psect
              , not $ Set.null ssect ]

zipSameKind :: SymbolRel -> Symbols -> Symbols -> Bool
zipSameKind rel s1 s2 = all id $ zipWith (sameKind rel) s1 s2

-- | True iff both Symbols are of the same Kind in the given Relation.
sameKind :: SymbolRel -> Symbol -> Symbol -> Bool
sameKind rel s1 s2
    | all id [isOpWildcard s1, isOperator s2] = True
    | all id [isOperator s1, isOpWildcard s2] = True
    | all isType [s1, s2] = typeSameKind rel s1 s2
    | all isOperator [s1, s2] = let
        Operator _ dom1 _ = s1
        Operator _ dom2 _ = s2
        in zipSameKind rel dom1 dom2
    | otherwise = False
