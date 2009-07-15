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

module Maude.Sign where

import Maude.AS_Maude
import Maude.Symbol

import Maude.Meta.HasName
import Maude.Meta.HasSorts
import Maude.Meta.HasOps

import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel

import qualified Common.Doc as Doc
import Common.DocUtils

import Maude.Printing


type SortSet = Set Symbol
type SubsortRel = Rel Symbol
type OpDecl = ([Symbol], Symbol, [Attr])
type OpDeclSet = Set OpDecl
type OpMap = Map Symbol OpDeclSet

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap
    } deriving (Show, Ord, Eq)


instance Pretty Sign where
  pretty sign = Doc.text $ printSign (sorts sign) (subsorts sign) (ops sign)


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


-- | extract the Signature of a Module
fromSpec :: Spec -> Sign
fromSpec (Spec _ _ stmts) = let
        insert stmt = case stmt of
            SortStmnt sort -> insertSort sort
            SubsortStmnt sub -> insertSubsort sub
            OpStmnt op -> insertOp op
            _ -> id
    in foldr insert empty stmts

-- | extract the Set of all Symbols from a Signature
symbols :: Sign -> SymbolSet
symbols sign = Set.union (getSorts sign) (getOps sign)

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
insertOpName :: OpId -> Sign -> Sign
insertOpName name sign = sign {ops = ins'opName name (ops sign)}

-- | insert an Operator declaration into a Signature
insertOp :: Operator -> Sign -> Sign
insertOp op sign = sign {ops = ins'op op (ops sign)}

-- | check that a Signature is legal
isLegal :: Sign -> Bool
isLegal sign = let
        isLegalSort sort = Set.member sort (sorts sign)
        isLegalOp (dom, cod, _) = all isLegalSort dom && isLegalSort cod
        legal'subsorts = Fold.all isLegalSort $ Rel.nodes (subsorts sign)
        legal'ops = Fold.all (Fold.all isLegalOp) (ops sign)
    in all id [legal'subsorts, legal'ops]


--- Helper functions for inserting Signature members into their respective collections.

-- insert a Sort into a Set of Sorts
ins'sort :: Sort -> SortSet -> SortSet
ins'sort = Set.insert . getName

-- insert a Subsort declaration into a Subsort Relationship
ins'subsort :: SubsortDecl -> SubsortRel -> SubsortRel
ins'subsort (Subsort sub super) = Rel.insert (getName sub) (getName super)

-- insert an Operator name into an Operator Map
ins'opName :: OpId -> OpMap -> OpMap
ins'opName op = Map.insert (getName op) Set.empty

-- insert an Operator declaration into an Operator Map
ins'op :: Operator -> OpMap -> OpMap
ins'op (Op op dom cod as) opmap = let
        name = getName op
        old'ops = Map.findWithDefault Set.empty name opmap
        new'ops = Set.insert (map getName dom, getName cod, as) old'ops
    in Map.insert name new'ops opmap


sig_union :: Sign -> Sign -> Sign
sig_union (Sign s1 ssr1 op1) (Sign s2 ssr2 op2) = Sign (sorts_union s1 s2)
                                                       (subsorts_union ssr1 ssr2)
                                                       (ops_union op1 op2)

sorts_union :: SortSet -> SortSet -> SortSet
sorts_union s1 s2 = Set.union s1 s2

subsorts_union :: SubsortRel -> SubsortRel -> SubsortRel
subsorts_union ssr1 ssr2 = Rel.union ssr1 ssr2

ops_union :: OpMap -> OpMap -> OpMap
ops_union op1 op2 = Map.union op1 op2

sig_int :: Sign -> Sign -> Sign
sig_int (Sign s1 ssr1 op1) (Sign s2 ssr2 op2) = Sign (sorts_int s1 s2)
                                                     (subsorts_int ssr1 ssr2)
                                                     (ops_int op1 op2)

sorts_int :: SortSet -> SortSet -> SortSet
sorts_int s1 s2 = Set.intersection s1 s2

subsorts_int :: SubsortRel -> SubsortRel -> SubsortRel
subsorts_int ssr1 ssr2 = Rel.fromDistinctMap $ Map.intersection (Rel.toMap ssr1) (Rel.toMap ssr2)

ops_int :: OpMap -> OpMap -> OpMap
ops_int op1 op2 = Map.intersection op1 op2

subsig :: Sign -> Sign -> Bool
subsig sign1 sign2 = sortsIncluded (sorts sign1) (sorts sign2) &&
                     subsortsIncluded (subsorts sign1) (subsorts sign2)

sortsIncluded :: SortSet -> SortSet -> Bool
sortsIncluded s1 s2 = Set.isSubsetOf s1 s2

subsortsIncluded :: SubsortRel -> SubsortRel -> Bool
subsortsIncluded ssr1 ssr2 = Rel.isSubrelOf ssr1 ssr2

opsIncluded :: OpMap -> OpMap -> Bool
opsIncluded op1 op2 = Map.isSubmapOf op1 op2

-- map and insert an OperatorMap key-value pair
map'op :: SymbolMap -> Symbol -> OpDeclSet -> OpMap -> OpMap
map'op mp op decls = Map.insert (Map.findWithDefault op op mp) decls
