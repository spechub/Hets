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
import Maude.Sentence
import Maude.Meta
import Maude.Util

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

-- | the union of two Signatures
union :: Sign -> Sign -> Sign
union sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.union sorts,
        subsorts = apply Rel.union subsorts,
        ops = apply Map.union ops
    }

-- | the intersection of two Signatures
intersection :: Sign -> Sign -> Sign
intersection sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.intersection sorts,
        subsorts = apply Rel.intersection subsorts,
        ops = apply Map.intersection ops
    }

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

-- | check that a Signature is a subsignature of another Signature
isSubsign :: Sign -> Sign -> Bool
isSubsign sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
        sorts'included = apply Set.isSubsetOf sorts
        subsorts'included = apply Rel.isSubrelOf subsorts
        ops'included = apply Map.isSubmapOf ops
    in all id [sorts'included, subsorts'included, ops'included]

-- | check that a Signature can include a Sentence
includesSentence :: Sign -> Sentence -> Bool
includesSentence sign sen = let
        ops'subset   = Set.isSubsetOf (getOps sen)   (getOps sign)
        sorts'subset = Set.isSubsetOf (getSorts sen) (getSorts sign)
    in all id [sorts'subset, ops'subset]

-- | simplification of sentences (leave out qualifications)
-- TODO: Add real implementation of simplification
simplifySentence :: Sign -> Sentence -> Sentence
simplifySentence _ = id


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

-- map and insert an OperatorMap key-value pair
map'op :: SymbolMap -> Symbol -> OpDeclSet -> OpMap -> OpMap
map'op mp op decls = Map.insert (mapAsFunction mp op) decls
