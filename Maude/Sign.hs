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
import Maude.Sentence
import Maude.Meta
import Maude.Util

import Maude.Symbol

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel

import qualified Common.Doc as Doc
import Common.DocUtils

import Maude.Printing


type SortSet = Set Qid
type SubsortRel = Rel Qid
type OpDecl = ([Qid], Qid, [Attr])
type OpDeclSet = Set OpDecl
type OpMap = Map Qid OpDeclSet

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap
    } deriving (Show, Ord, Eq)


instance Pretty Sign where
  pretty sign = Doc.text $ "\n" ++ printSign (sorts sign) (subsorts sign) (ops sign)


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
fromSpec :: Module -> Sign
fromSpec (Module _ _ stmts) = let
        insert stmt = case stmt of
            SortStmnt sort -> insertSort sort
            SubsortStmnt sub -> insertSubsort sub
            OpStmnt op -> insertOp op
            _ -> id
    in foldr insert empty stmts

-- | extract the Set of all Qids from a Signature
symbols :: Sign -> SymbolSet
symbols sign = Set.union (sorts2symbols $ sorts sign) (ops2symbols $ ops sign)

sorts2symbols :: Set Qid -> SymbolSet
sorts2symbols = Set.map (\ x -> Sort x)

ops2symbols :: OpMap -> SymbolSet
ops2symbols _ = Set.empty

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

-- | rename the given sort
renameListSort :: [(Qid, Qid)] -> Sign -> Sign
renameListSort rnms sg = foldr f sg rnms
              where f = \ (x, y) z -> renameSort x y z

-- | rename the given sort
renameSort :: Qid -> Qid -> Sign -> Sign
renameSort from to sign = Sign sorts' subsorts' ops'
              where sorts' = ren'sort'sortset from to $ sorts sign
                    subsorts' = ren'sort'subsortrel from to $ subsorts sign
                    ops' = ren'sort'op_map from to $ ops sign

-- | rename the given sort
renameOp :: Qid -> Qid -> [Attr] -> Sign -> Sign
renameOp from to ats sign = sign {ops = ops'}
              where ops' = ren'op'op_map from to ats $ ops sign

-- | rename the sort with the given profile
renameOpProfile :: Qid -> [Qid] -> Qid -> Qid -> [Attr] -> Sign -> Sign
renameOpProfile from ar co to ats sg = case Map.member from (ops sg) of
                            False -> sg
                            True -> sg

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
map'op :: Map Qid Qid -> Qid -> OpDeclSet -> OpMap -> OpMap
map'op mp op decls = Map.insert (mapAsFunction mp op) decls

-- | rename a sort in a sortset
ren'sort'sortset :: Qid -> Qid -> SortSet -> SortSet 
ren'sort'sortset from to = Set.insert to . Set.delete from

-- | rename a sort in a subsort relation
ren'sort'subsortrel :: Qid -> Qid -> SubsortRel -> SubsortRel 
ren'sort'subsortrel from to ssr = Rel.fromList ssr''
                where ssr' = Rel.toList ssr
                      ssr'' = map (ren'pair from to) ssr'

-- | aux function that renames pair
ren'pair :: Qid -> Qid -> (Qid, Qid) -> (Qid, Qid)
ren'pair from to (s1, s2) = if from == s1
                            then (to, s2)
                            else if from == s2
                                 then (s1, to)
                                 else (s1, s2)

-- | rename a sort in an operator map
ren'sort'op_map :: Qid -> Qid -> OpMap -> OpMap
ren'sort'op_map from to = Map.map (ren'sort'ops from to)

-- | rename a sort in a set of operator declarations
ren'sort'ops :: Qid -> Qid -> OpDeclSet -> OpDeclSet
ren'sort'ops from to = Set.map $ ren'op from to

-- | aux function to rename operator declarations
ren'op :: Qid -> Qid -> OpDecl -> OpDecl
ren'op from to (ar, coar, ats) = (ar', coar', ats)
             where ar' = map (\ x -> if x == from then to else x) ar
                   coar' = if from == coar
                           then to
                           else coar

-- | rename an operator in an operator map
ren'op'op_map :: Qid -> Qid -> [Attr] -> OpMap -> OpMap
ren'op'op_map from to ats = Map.fromList . map f . Map.toList
               where f = \ (x,y) -> if x == from 
                                    then (to,ren'op'set ats y)
                                    else (x,y)

-- | rename the attributes in the operator declaration set
ren'op'set :: [Attr] -> OpDeclSet -> OpDeclSet
ren'op'set ats ods = Set.map f ods
               where f = \ (x, y, z) -> (x, y, ren'op'ats ats z)

-- | rename the attributes in an attribute set
ren'op'ats :: [Attr] -> [Attr] -> [Attr]
ren'op'ats [] curr_ats = curr_ats
ren'op'ats (at : ats) curr_ats = ren'op'ats ats $ ren'op'at at curr_ats

-- | renama an attribute in an attribute set
ren'op'at :: Attr -> [Attr] -> [Attr]
ren'op'at rn@(Prec i) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Prec _ -> Prec i
                             at -> at
ren'op'at rn@(Gather qs) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Gather _ -> Gather qs
                             at -> at
ren'op'at rn@(Format qs) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Format _ -> Format qs
                             at -> at
ren'op'at _ _ = []

applySortMap :: Map Qid Qid -> Sign -> Sign
applySortMap sm sg = sg {
                  sorts = Set.map f $ sorts sg,
                  subsorts = Rel.fromList $ map g $ Rel.toList $ subsorts sg
                  -- TODO: add renaming in operators
                  }
        where f = \ x -> if Map.member x sm
                         then fromJust $ Map.lookup x sm
                         else x
              g = \ (x, y) -> if Map.member x sm
                              then if Map.member y sm
                                   then (fromJust $ Map.lookup x sm, fromJust $ Map.lookup y sm)
                                   else (fromJust $ Map.lookup x sm, y)
                              else if Map.member y sm
                                   then (x, fromJust $ Map.lookup y sm)
                                   else (x, y)
