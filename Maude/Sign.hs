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
    labels,
    opNames,
    empty,
    insertSort,
    insertSubsort,
    insertOpName,
    insertOp,
    isLegal,
) where

import Maude.Meta

import qualified Data.Foldable as Fold
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Lib.Rel as Rel

type SubsortRel = Rel.Rel Sort
type OpMap = Map.Map Qid OpDeclSet

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap
    } deriving (Show, Eq)

-- | extract the Signature of a Module
fromMod :: (Module a) => a -> Sign
fromMod modul = let
        mk'subsorts = Rel.transClosure . Set.fold ins'subsort Rel.empty
        mk'ops = Set.fold ins'op Map.empty
    in Sign {
        sorts = getSorts modul,
        subsorts = mk'subsorts (getSubsorts modul),
        ops = mk'ops (getOps modul)
    }

-- | extract the Set of labels of a Signature's Set of Operators
labels :: Sign -> QidSet
labels = let
        combine = Set.union . Set.fold insert Set.empty . Set.map extract
        extract (Label label) = Just label
        extract _ = Nothing
        insert (Just label) = Set.insert label
        insert _ = id
        fold = Fold.foldr (combine . op'attrs) Set.empty
    in fold . Set.unions . Map.elems . ops

-- | extract the Set of Operator names of a Signature's Set of Operators
opNames :: Sign -> QidSet
opNames = Map.keysSet . ops

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
insertOpName :: Qid -> Sign -> Sign
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


--- Helper functions for inserting Signature members into their respective collections.

-- insert a Sort into a Set of Sorts
ins'sort :: Sort -> SortSet -> SortSet
ins'sort sort set = Set.insert sort set

-- insert a Subsort declaration into a Subsort Relationship
ins'subsort :: SubsortDecl -> SubsortRel -> SubsortRel
ins'subsort sub rel = Rel.insert (subsort sub) (supersort sub) rel

-- insert an Operator name into an Operator Map
ins'opName :: Qid -> OpMap -> OpMap
ins'opName name opmap = Map.insert name Set.empty opmap

-- insert an Operator declaration into an Operator Map
ins'op :: OpDecl -> OpMap -> OpMap
ins'op op opmap = let
        name = op'name op
        old'ops = Map.findWithDefault Set.empty name opmap
        new'ops = Set.insert op old'ops
    in Map.insert name new'ops opmap
