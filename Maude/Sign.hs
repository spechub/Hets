{- |
Module      :  $Header$
Description :  Signatures for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for Maude.
-}

module Maude.Sign (
    Sign(..),
    SortSet,
    SubsortRel,
    OpDecl,
    OpDeclSet,
    OpMap,
    Sentences,
    fromSpec,
    symbols,
    empty,
    union,
    intersection,
    isLegal,
    isSubsign,
    includesSentence,
    simplifySentence,
    renameSort,
    renameLabel,
    renameOp,
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta
import Maude.Printing ()

import Maude.Sentence (Sentence)
import qualified Maude.Sentence as Sen

import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Foldable as Fold
import qualified Common.Lib.Rel as Rel

import Common.Doc hiding (empty)
import Common.DocUtils (Pretty(..))


type SortSet = SymbolSet
type SubsortRel = SymbolRel
type OpDecl = (Symbol, [Attr])
type OpDeclSet = Set (Set OpDecl)
type OpMap = Map Qid OpDeclSet
type Sentences = Set Sentence

-- TODO: Should we also add the Module name to Sign?
data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap,
        sentences :: Sentences
    } deriving (Show, Ord, Eq)


instance Pretty Sign where
    pretty sign = let
            descend = flip . Set.fold
            -- print sort declarations
            pr'sorts ss = hsep
                [keyword "sorts", hsep $ map pretty ss, dot]
            -- print subsort declarations
            pr'sups = hsep . map pretty . Set.elems
            pr'pair sub sups = (:) . hsep $
                [keyword "subsort", pretty sub, less, pr'sups sups]
            pr'subs = vsep . Map.foldWithKey pr'pair []
            -- print operator decparations
            pr'decl (symb, attrs) = hsep
                [keyword "op", pretty symb, pretty attrs, dot]
            pr'ods = descend ((:) . pr'decl)
            pr'ocs = descend pr'ods
            pr'ops = vsep . Map.fold pr'ocs []
        in vsep [
            pr'sorts $ Set.elems $ sorts sign,
            -- TODO: We might want print just the transitively minimal subsort relation.
            pr'subs $ Rel.toMap $ subsorts sign,
            pr'ops $ ops sign,
            pretty $ sentences sign
        ]


instance HasSorts Sign where
    getSorts = sorts
    mapSorts mp sign = sign {
        sorts = mapSorts mp $ sorts sign,
        subsorts = mapSorts mp $ subsorts sign,
        ops = mapSorts mp $ ops sign
        -- NOTE: Leaving out Sentence for now. :-)
    }


instance HasOps Sign where
    getOps = let
            descend = flip . Set.fold
            insert = descend $ descend $ Set.insert . fst
        in Map.fold insert Set.empty . ops
    -- TODO: I really dislike doing this pairwise...
    mapOps mp sign = let
            subrel = subsorts sign
            opmap = ops sign
            update src tgt = mapOpDecl subrel src tgt []
        in sign {
            ops = Map.foldWithKey update opmap mp
        }

instance HasLabels Sign where
    getLabels = getLabels . sentences
    mapLabels mp sign = sign {
        sentences = mapLabels mp $ sentences sign
    }


partitionStmts :: [Statement] -> ([Sort], [SubsortDecl], [Operator])
partitionStmts = let
        switch (sorts', subs', ops') stmt = case stmt of
            SortStmnt sort -> (sort:sorts', subs', ops')
            SubsortStmnt sub -> (sorts', sub:subs', ops')
            OpStmnt op -> (sorts', subs', op:ops')
            _ -> (sorts', subs', ops')
    in foldl switch ([], [], [])

-- | Extract the Signature of a Module.
fromSpec :: Module -> Sign
fromSpec spec@(Module _ _ stmts) = let
        sents = filter (not . Sen.isRule) . Sen.fromSpec $ spec
        (sort'list, sub'list, op'list) = partitionStmts stmts
        sign0 = empty
        sign1 = foldr insertSort sign0 sort'list
        sign2 = foldr insertSubsort sign1 sub'list
        sign  = foldr insertOp sign2 op'list
    in sign {
        subsorts = Rel.transClosure $ subsorts sign,
        sentences = Set.fromList sents
    }

-- | Extract the Set of all Symbols from a Signature.
symbols :: Sign -> SymbolSet
symbols sign = Set.unions [
        getSorts sign,
        getOps sign,
        getLabels sign
    ]

-- | The empty Signature.
empty :: Sign
empty = Sign {
    sorts = Set.empty,
    subsorts = Rel.empty,
    ops = Map.empty,
    sentences = Set.empty
}

-- | The union of two Signatures.
union :: Sign -> Sign -> Sign
union sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.union sorts,
        subsorts = apply Rel.union subsorts,
        ops = apply Map.union ops,
        sentences = apply Set.union sentences
    }

-- | The intersection of two Signatures.
intersection :: Sign -> Sign -> Sign
intersection sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.intersection sorts,
        subsorts = apply Rel.intersection subsorts,
        ops = apply Map.intersection ops,
        sentences = apply Set.intersection sentences
    }


-- | Insert a Sort into a Signature.
insertSort :: Sort -> Sign -> Sign
insertSort sort sign = let
        insert = Set.insert . asSymbol
    in sign {sorts = insert sort (sorts sign)}

-- | Insert a Subsort declaration into a Signature.
insertSubsort :: SubsortDecl -> Sign -> Sign
insertSubsort decl sign = let
        insert (Subsort sub super) = Rel.insert (asSymbol sub) (asSymbol super)
    in sign {subsorts = insert decl (subsorts sign)}

-- | Insert an Operator declaration into an OperatorMap.
insertOpDecl :: SymbolRel -> Symbol -> [Attr] -> OpMap -> OpMap
insertOpDecl rel symb attrs opmap = let
        name = getName symb
        decl = Set.singleton (symb, attrs)
        same'kind = Fold.any $ sameKind rel symb . fst
        old'ops = Map.findWithDefault Set.empty name opmap
        (same, rest) = Set.partition same'kind old'ops
        new'decl = Set.fold Set.union decl same
        new'ops = Set.insert new'decl rest
    in Map.insert name new'ops opmap

-- TODO: Handle renamings which change Attrs.
-- TODO: I'm not sure whether this is the right way...
mapOpDecl :: SymbolRel -> Symbol -> Symbol -> [Attr] -> OpMap -> OpMap
mapOpDecl rel src tgt _ opmap = let
        set'union = Set.fold Set.union Set.empty
        src'name = getName src
        tgt'name = getName tgt
        same'kind = Fold.any $ sameKind rel src . fst
        src'ops = Map.findWithDefault Set.empty src'name opmap
        tgt'ops = Map.findWithDefault Set.empty tgt'name opmap
        (same, rest) = Set.partition same'kind src'ops
        new'decl = mapOps (Map.singleton src tgt) $ set'union same
        up'rest = const $ if Set.null rest
            then Nothing
            else Just rest
        set'rest = Map.update up'rest src'name
        set'decl = Map.insert tgt'name $ Set.insert new'decl tgt'ops
    in set'rest . set'decl $ opmap

-- | Insert an Operator declaration into a Signature.
insertOp :: Operator -> Sign -> Sign
insertOp op sign = let
        subrel = subsorts sign
        insert (Op _ _ _ as) = insertOpDecl subrel (asSymbol op) as
    in sign {ops = insert op $ ops sign}


-- TODO: Add more checks, e.g. whether all Symbols in SortSet are Sorts?
-- | Check that a Signature is legal.
isLegal :: Sign -> Bool
isLegal sign = let
        has'sort sort = Set.member (asSort sort) (sorts sign)
        has'subsorts = Fold.all has'sort . getSorts $ subsorts sign
        has'ops = Fold.all has'sort . getSorts $ ops sign
    in all id [has'subsorts, has'ops]

-- | Check that a Signature is a subsignature of another Signature.
isSubsign :: Sign -> Sign -> Bool
isSubsign sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
        has'sorts = apply Set.isSubsetOf sorts
        has'subsorts = apply Rel.isSubrelOf subsorts
        has'ops = apply Map.isSubmapOf ops
    in all id [has'sorts, has'subsorts, has'ops]

-- | Check that a Signature can include a Sentence
includesSentence :: Sign -> Sentence -> Bool
includesSentence sign sen = let
        apply func a1 a2 = func (a1 sen) (a2 sign)
        has'ops   = apply Set.isSubsetOf getOps getOps
        has'sorts = apply Set.isSubsetOf getSorts getSorts
    in all id [has'sorts, has'ops]

-- TODO: Add real implementation of simplification. Maybe.
-- | Simplification of sentences (leave out qualifications)
simplifySentence :: Sign -> Sentence -> Sentence
simplifySentence _ = id



-- | Rename the given Sort in the given Signature.
renameSort :: Symbol -> Symbol -> Sign -> Sign
renameSort from to = mapSorts $ Map.singleton from to

-- | Rename the given Label in the given Signature.
renameLabel :: Symbol -> Symbol -> Sign -> Sign
renameLabel from to = mapLabels $ Map.singleton from to

-- renameOpProfile corresponds with this function not, as the profile is
-- contained in the Symbol type.
-- TODO: Handle renamings which change Attrs.
-- | Rename the given Operator in the given Signature.
renameOp :: Symbol -> Symbol -> [Attr] -> Sign -> Sign
renameOp from to _ = mapOps $ Map.singleton from to

-- TODO: Our current Symbols don't include Attributes, so we can't use
-- SymbolMaps to replicate this functionality...
-- -- | rename the attributes in an attribute set
-- ren'op'ats :: [Attr] -> [Attr] -> [Attr]
-- ren'op'ats [] curr_ats = curr_ats
-- ren'op'ats (at : ats) curr_ats = ren'op'ats ats $ ren'op'at at curr_ats
-- 
-- -- | rename an attribute in an attribute set
-- ren'op'at :: Attr -> [Attr] -> [Attr]
-- ren'op'at rn@(Prec i) (a : ats) = a' : ren'op'at rn ats
--                where a' = case a of
--                              Prec _ -> Prec i
--                              at -> at
-- ren'op'at rn@(Gather qs) (a : ats) = a' : ren'op'at rn ats
--                where a' = case a of
--                              Gather _ -> Gather qs
--                              at -> at
-- ren'op'at rn@(Format qs) (a : ats) = a' : ren'op'at rn ats
--                where a' = case a of
--                              Format _ -> Format qs
--                              at -> at
-- ren'op'at _ _ = []
