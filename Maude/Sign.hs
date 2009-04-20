{- |
Module      :  $Header$
Description :  Signatures for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Sign (
    Sign(..),
    fromMod,
    symbols,
    empty,
    insertSort,
    insertSubsort,
    insertOpName,
    insertOp,
    isLegal,
    includesSentence,
    simplifySentence,
) where

import Maude.Meta
import Maude.Symbol
import Maude.Sentence

import Data.Typeable (Typeable)
import qualified Data.Foldable as Fold
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Common.Lib.Rel as Rel

-- for ShATermConvertible
import Common.ATerm.Conversion
-- for Pretty
import Common.DocUtils (Pretty(..))
import qualified Common.Doc as Doc


type SubsortRel = Rel.Rel Sort
type OpMap = Map.Map Symbol OpDeclSet

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap
    } deriving (Show, Eq, Ord, Typeable)

-- TODO: Add real pretty-printing for Maude Signatures.
instance Pretty Sign where
    pretty _ = Doc.empty

-- TODO: Replace dummy implementation for ShATermConvertible Sign.
instance ShATermConvertible Sign where
    toShATermAux table _ = return (table, 0)
    fromShATermAux _ table = (table, empty)


instance HasSorts Sign where
    getSorts = sorts
    mapSorts mp sign = sign {
        sorts = mapSorts mp (sorts sign),
        subsorts = mapSorts mp (subsorts sign)
    }

instance HasOps Sign where
    getOps = Map.keysSet . ops
    mapOps mp sign = sign {
        ops = Map.foldWithKey (map'op mp) Map.empty (ops sign)
    }

instance HasLabels Sign where
    getLabels = getLabels . Map.elems . ops
    mapLabels mp sign = sign {
        ops = Map.map (mapLabels mp) (ops sign)
    }


-- | extract the Signature of a Module
fromMod :: (Module a) => a -> Sign
fromMod modul = let
        mk'subsorts = Rel.transClosure . Set.fold ins'subsort Rel.empty
        mk'ops = Set.fold ins'op Map.empty
    in Sign {
        sorts = modSorts modul,
        subsorts = mk'subsorts (modSubsorts modul),
        ops = mk'ops (modOps modul)
    }

-- | extract the Set of all Symbols from a Signature
symbols :: Sign -> SymbolSet
symbols sign = Set.unions [(getSorts sign), (getOps sign), (getLabels sign)]

-- | the empty Signature
empty :: Sign
empty = Sign { sorts = Set.empty, subsorts = Rel.empty, ops = Map.empty }

-- | insert a Sort into a Signature
insertSort :: Sort -> Sign -> Sign
insertSort sort sign = sign {sorts = ins'sort sort (sorts sign)}

-- | insert a Subsort declaration into a Signature
insertSubsort :: SubsortDecl -> Sign -> Sign
insertSubsort decl sign = sign {subsorts = ins'subsort decl (subsorts sign)}

-- | insert an Operator name into a Signature
insertOpName :: Symbol -> Sign -> Sign
insertOpName name sign = sign {ops = ins'opName name (ops sign)}

-- | insert an Operator declaration into a Signature
insertOp :: OpDecl -> Sign -> Sign
insertOp op sign = sign {ops = ins'op op (ops sign)}

-- | check that a Signature is legal
isLegal :: Sign -> Bool
isLegal sign = let
        isLegalType typ = case typ of
            Kind kind -> not $ null kind && all isLegalSort kind
            -- TODO: Check that all sorts are in the same connected component.
            Sort sort  -> isLegalSort sort
        isLegalSort sort = Set.member sort (sorts sign)
        isLegalOp op = isLegalType (op'domain op) && all isLegalType (op'range op)
        legal'subsorts = Fold.all isLegalSort $ Rel.nodes (subsorts sign)
        legal'ops = Fold.all (Fold.all isLegalOp) (ops sign)
    in all id [legal'subsorts, legal'ops]

-- | check that a Signature can include a Sentence
includesSentence :: Sign -> Sentence -> Bool
includesSentence sign sen = let
        ops'subset    = Set.isSubsetOf (getOps sen)    (getOps sign)
        sorts'subset  = Set.isSubsetOf (getSorts sen)  (getSorts sign)
        labels'subset = Set.isSubsetOf (getLabels sen) (getLabels sign)
    in all id [sorts'subset, ops'subset, labels'subset]

-- | simplification of sentences (leave out qualifications)
-- TODO: Add real implementation of simplification
simplifySentence :: Sign -> Sentence -> Sentence
simplifySentence _ = id

--- Helper functions for inserting Signature members into their respective collections.

-- insert a Sort into a Set of Sorts
ins'sort :: Sort -> SortSet -> SortSet
ins'sort sort set = Set.insert sort set

-- insert a Subsort declaration into a Subsort Relationship
ins'subsort :: SubsortDecl -> SubsortRel -> SubsortRel
ins'subsort sub rel = Rel.insert (subsort sub) (supersort sub) rel

-- insert an Operator name into an Operator Map
ins'opName :: Symbol -> OpMap -> OpMap
ins'opName name opmap = Map.insert name Set.empty opmap

-- insert an Operator declaration into an Operator Map
ins'op :: OpDecl -> OpMap -> OpMap
ins'op op opmap = let
        name = op'name op
        old'ops = Map.findWithDefault Set.empty name opmap
        new'ops = Set.insert op old'ops
    in Map.insert name new'ops opmap

-- map an OperatorMap key-value pair and insert it into the accumulator
map'op :: SymbolMap -> Symbol -> OpDeclSet -> OpMap -> OpMap
map'op mp op decls acc = let
        key = mapToFunction mp op
        val = mapOps mp decls
    in Map.insert key val acc


mapToFunction :: (Ord a) => Map.Map a a -> (a -> a)
mapToFunction mp name = Map.findWithDefault name name mp
