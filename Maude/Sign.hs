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

import Data.Set (Set)
import Data.Map (Map)
import Data.Typeable (Typeable)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

import Common.Id (Token)
import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel


type SortSet = Set Token
type SubsortRel = Rel Token
type OpMap = Map Token (Set ([Token], Token))

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap
    } deriving Show--(Show, Eq, Ord, Typeable)


-- | extract the Signature of a Module
fromSpec :: Spec -> Sign
fromSpec (Spec _ _ stmts) = let
        insert stmt = case stmt of
            SortStmnt sort -> insertSort sort
            SubsortStmnt subsort -> insertSubsort subsort
            OpStmnt op -> insertOp op
            _ -> id
    in foldr insert empty stmts

-- | extract the Set of all Symbols from a Signature
symbols :: Sign -> Set Token
symbols sign = Set.unions [(sorts sign), (Map.keysSet $ ops sign)]

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
        isLegalOp (dom, cod) = all isLegalSort dom && isLegalSort cod
        legal'subsorts = Fold.all isLegalSort $ Rel.nodes (subsorts sign)
        legal'ops = Fold.all (Fold.all isLegalOp) (ops sign)
    in all id [legal'subsorts, legal'ops]


--- Helper functions for inserting Signature members into their respective collections.

-- insert a Sort into a Set of Sorts
ins'sort :: Sort -> SortSet -> SortSet
ins'sort = Set.insert . sortName

-- insert a Subsort declaration into a Subsort Relationship
ins'subsort :: SubsortDecl -> SubsortRel -> SubsortRel
ins'subsort (Subsort sub super) = Rel.insert (sortName sub) (sortName super)

-- insert an Operator name into an Operator Map
ins'opName :: OpId -> OpMap -> OpMap
ins'opName (OpId name) = Map.insert name Set.empty

-- insert an Operator declaration into an Operator Map
ins'op :: Operator -> OpMap -> OpMap
ins'op op opmap = let
        Op opid dom cod _ = op
        OpId name = opid
        old'ops = Map.findWithDefault Set.empty name opmap
        new'ops = Set.insert (map typeName dom, typeName cod) old'ops
    in Map.insert name new'ops opmap

-- extract the name from a Sort, Kind or Type
sortName (SortId name) = name
kindName (KindId name) = name
typeName (TypeSort sort) = sortName sort
typeName (TypeKind kind) = kindName kind
