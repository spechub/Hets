{- |
Module      :  $Header$
Description :  Symbols for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of symbols for Maude.
-}

module Maude.Symbol (
    Symbol(..),
    Symbols,
    SymbolSet,
    SymbolMap,
    SymbolRel,
    toId,
    toType,
    toOperator,
    mkOpTotal,
    mkOpPartial,
    sameKind,
    zipSameKind,
) where


import Maude.AS_Maude
import Maude.Meta.HasName

import Data.Set (Set)
import Data.Map (Map)
import Common.Lib.Rel (Rel)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

import Data.Maybe (fromJust)
import Common.Id (Id, mkId, GetRange, getRange, nullRange)

import Common.Doc
import Common.DocUtils (Pretty(..))


data Symbol = Sort Qid
            | Kind Qid
            | Labl Qid
            | Operator Qid Symbols Symbol
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
        Operator qid _ _ -> qid
    mapName mp symb = case symb of
        Sort qid -> Sort $ mapName mp qid
        Kind qid -> Kind $ mapName mp qid
        Labl qid -> Labl $ mapName mp qid
        Operator qid dom cod -> Operator (mapName mp qid) dom cod


opDecl :: Qid -> [Symbol] -> Symbol -> Doc -> Doc
opDecl qid dom cod arr = hsep
    [pretty qid, colon, hsep $ map pretty dom, arr, pretty cod]
instance Pretty Symbol where
    pretty symb = case symb of
        Sort qid -> pretty qid
        Kind qid -> pretty qid
        Labl qid -> pretty qid
        Operator qid dom cod -> case cod of
            Sort _ -> opDecl qid dom cod funArrow
            Kind _ -> opDecl qid dom cod $ text "~>"
            _ -> empty


instance GetRange Symbol where
    getRange _ = nullRange


toId :: Symbol -> Id
toId = mkId . return . getName


toTypeMaybe :: Symbol -> Maybe Type
toTypeMaybe symb = case symb of
    Sort qid -> Just . TypeSort . SortId $ qid
    Kind qid -> Just . TypeKind . KindId $ qid
    _ -> Nothing

toType :: Symbol -> Type
toType = fromJust . toTypeMaybe

toOperatorMaybe :: Symbol -> Maybe Operator
toOperatorMaybe symb = case symb of
    Operator qid dom cod -> Just $
        Op (OpId qid) (map toType dom) (toType cod) []
    _ -> Nothing

toOperator :: Symbol -> Operator
toOperator = fromJust . toOperatorMaybe

mkOpTotal :: Qid -> [Qid] -> Qid -> Symbol
mkOpTotal qid dom cod = Operator qid (map Sort dom) (Sort cod)

mkOpPartial :: Qid -> [Qid] -> Qid -> Symbol
mkOpPartial qid dom cod = Operator qid (map Sort dom) (Kind cod)


zipSameKind :: SymbolRel -> Symbols -> Symbols -> Bool
zipSameKind rel s1 s2 = all id . zipWith (sameKind rel) $ s1 s2

sameKind :: SymbolRel -> Symbol -> Symbol -> Bool
sameKind rel s1 s2 = let
        preds1 = Rel.predecessors rel s1
        preds2 = Rel.predecessors rel s2
        succs1 = Rel.succs rel s1
        succs2 = Rel.succs rel s2
        psect  = Set.intersection preds1 preds2
        ssect  = Set.intersection succs1 succs2
    in any id [
        s1 == s2,
        Set.member s2 preds1,
        Set.member s1 preds2,
        Set.member s2 succs1,
        Set.member s1 succs2,
        not $ Set.null psect,
        not $ Set.null ssect
    ]
