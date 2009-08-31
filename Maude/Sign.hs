{- |
Module      :  $Header$
Description :  Maude Signatures
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for Maude.
-}

module Maude.Sign (
    -- * Types
    -- ** The Signature type
    Sign(..),
    -- ** Auxiliary types
    SortSet,
    SubsortRel,
    OpDecl,
    OpDeclSet,
    OpMap,
    Sentences,
    -- * Construction
    fromSpec,
    empty,
    -- * Combination
    union,
    intersection,
    -- * Conversion
    symbols,
    -- * Testing
    isLegal,
    isSubsign,
    includesSentence,
    -- * Modification
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

-- * Types

-- ** Auxiliary types

type SortSet = SymbolSet
type SubsortRel = SymbolRel
type OpDecl = (Set Symbol, [Attr])
type OpDeclSet = Set OpDecl
type OpMap = Map Qid OpDeclSet
type Sentences = Set Sentence

-- TODO: Add the Module name to Sign. Maybe.
-- ** The Signature type
-- | The Signature of a Maude 'Module'.
data Sign = Sign {
        sorts :: SortSet,               -- ^ The 'Set' of 'Sort's
        subsorts :: SubsortRel,         -- ^ The 'Rel'ation of 'Sort's
        ops :: OpMap,                   -- ^ The 'Map' of 'Operator's
        sentences :: Sentences          -- ^ The 'Set' of 'Sentence's
    } deriving (Show, Ord, Eq)

-- ** 'Sign' instances

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
        pr'subs = vcat . Map.foldWithKey pr'pair []
        -- print operator decparations
        pr'decl attrs symb = hsep
            [keyword "op", pretty symb, pretty attrs, dot]
        pr'ods (decls, attrs) = descend ((:) . pr'decl attrs) decls
        pr'ocs = descend pr'ods
        pr'ops = vcat . Map.fold pr'ocs []
        in vcat [ pr'sorts $ Set.elems $ sorts sign
                , pr'subs $ Rel.toMap $ Rel.transReduce $ subsorts sign
                , pr'ops $ ops sign ]
                -- NOTE: Leaving out Sentences for now.
                -- , pretty $ Set.toList $ sentences sign ]

instance HasSorts Sign where
    getSorts = sorts
    mapSorts mp sign = sign {
        sorts = mapSorts mp $ sorts sign,
        subsorts = mapSorts mp $ subsorts sign,
        ops = mapSorts mp $ ops sign
        -- NOTE: Leaving out Sentences for now.
        -- sentences = mapSorts mp $ sentences sign
    }

instance HasOps Sign where
    getOps = let
        descend = flip . Set.fold
        insert = descend $ descend Set.insert . fst
        in Map.fold insert Set.empty . ops
    mapOps mp sign = let
        subrel = subsorts sign
        opmap = ops sign
        update src tgt = mapOpDecl subrel src tgt []
        in sign {
            ops = Map.foldWithKey update opmap mp
            -- NOTE: Leaving out Sentences for now.
        }

instance HasLabels Sign where
    getLabels = getLabels . sentences
    mapLabels mp sign = sign {
        sentences = mapLabels mp $ sentences sign
    }

-- * Construction

-- | Separate Sort, Subsort and Operator declaration 'Statement's.
partitionStmts :: [Statement] -> ([Sort], [SubsortDecl], [Operator])
partitionStmts = let
    switch (sorts', subs', ops') stmt = case stmt of
        SortStmnt sort -> (sort:sorts', subs', ops')
        SubsortStmnt sub -> (sorts', sub:subs', ops')
        OpStmnt op -> (sorts', subs', op:ops')
        _ -> (sorts', subs', ops')
    in foldl switch ([], [], [])

-- | Extract the 'Sign'ature from the given 'Module'.
fromSpec :: Module -> Sign
fromSpec (Module _ _ stmts) = let
    sents = filter (not . Sen.isRule) . Sen.fromStatements $ stmts
    (sort'list, sub'list, op'list) = partitionStmts stmts
    ins'sorts = flip (foldr insertSort) sort'list
    ins'subs  = flip (foldr insertSubsort) sub'list
    ins'ops   = flip (foldr insertOp) op'list
    sign = ins'ops . ins'subs . ins'sorts $ empty
    in sign {
        subsorts = Rel.transClosure $ subsorts sign,
        sentences = Set.fromList sents
    }

-- | The empty 'Sign'ature.
empty :: Sign
empty = Sign {
    sorts = Set.empty,
    subsorts = Rel.empty,
    ops = Map.empty,
    sentences = Set.empty
}

-- ** Auxiliary construction

-- | Insert a 'Sort' into a 'Sign'ature.
insertSort :: Sort -> Sign -> Sign
insertSort sort sign = let
    insert = Set.insert . asSymbol
    in sign {sorts = insert sort (sorts sign)}

-- | Insert a 'SubsortDecl' into a 'Sign'ature.
insertSubsort :: SubsortDecl -> Sign -> Sign
insertSubsort decl sign = let
    insert (Subsort sub super) = Rel.insert (asSymbol sub) (asSymbol super)
    in sign {subsorts = insert decl (subsorts sign)}

-- | Insert an 'Operator' declaration into an 'Operator' 'Map'.
insertOpDecl :: SymbolRel -> Symbol -> [Attr] -> OpMap -> OpMap
insertOpDecl rel symb attrs opmap = let
    merge decls = let
        decl = head $ Set.toList decls
        syms = Set.insert symb $ fst decl
        attr = mergeAttrs attrs $ snd decl
        in if Set.null decls
           then Set.insert (asSymbolSet symb, attrs)
           else Set.insert (syms, attr)
    name = getName symb
    same'kind = Fold.any (sameKind rel symb) . fst
    old'ops = Map.findWithDefault Set.empty name opmap
    (same, rest) = Set.partition same'kind old'ops
    new'ops = merge same rest
    in Map.insert name new'ops opmap

-- | Map 'Operator' declarations of the given 'Kind' in an 'Operator' 'Map'.
mapOpDecl :: SymbolRel -> Symbol -> Symbol -> [Attr] -> OpMap -> OpMap
mapOpDecl rel src tgt attrs opmap = let
    merge decls = let
        decl = head $ Set.toList decls
        syms = mapOps (Map.singleton src tgt) $ fst decl
        attr = mergeAttrs attrs $ snd decl
        in if Set.null decls
           then id
           else Set.insert (syms, attr)
    src'name = getName src
    tgt'name = getName tgt
    same'kind = Fold.any (sameKind rel src) . fst
    src'ops = Map.findWithDefault Set.empty src'name opmap
    tgt'ops = Map.findWithDefault Set.empty tgt'name opmap
    (same, rest) = Set.partition same'kind src'ops
    has'rest = if Set.null rest then Nothing else Just rest
    set'decl = Map.insert tgt'name $ merge same tgt'ops
    set'rest = Map.update (const has'rest) src'name
    in set'rest . set'decl $ opmap

-- | Insert an 'Operator' declaration into a 'Sign'ature.
insertOp :: Operator -> Sign -> Sign
insertOp op sign = let
    subrel = subsorts sign
    insert (Op _ _ _ as) = insertOpDecl subrel (asSymbol op) as
    in sign {ops = insert op $ ops sign}

-- | Merge new 'Attr'ibutes with the old ones.
mergeAttrs :: [Attr] -> [Attr] -> [Attr]
mergeAttrs = let
    similar (Prec _)   (Prec _)   = True
    similar (Gather _) (Gather _) = True
    similar (Format _) (Format _) = True
    -- Other Attributes don't change in Renamings.
    similar _ _ = False
    update new = (:) new . filter (not . similar new)
    in flip $ foldl $ flip update

-- * Combination

-- | The union of two 'Sign'atures.
union :: Sign -> Sign -> Sign
union sig1 sig2 = let
    apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.union sorts,
        subsorts = apply Rel.union subsorts,
        ops = apply (Map.unionWith Set.union) ops,
        sentences = apply Set.union sentences
    }

-- | The intersection of two 'Sign'atures.
intersection :: Sign -> Sign -> Sign
intersection sig1 sig2 = let
    apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.intersection sorts,
        subsorts = apply Rel.intersection subsorts,
        ops = apply Map.intersection ops,
        sentences = apply Set.intersection sentences
    }

-- * Conversion

-- | Extract the 'Set' of all 'Symbol's from a 'Sign'ature.
symbols :: Sign -> SymbolSet
symbols sign = Set.unions [ getSorts sign, getOps sign, getLabels sign ]

-- * Testing

-- TODO: Add more checks, e.g. whether all Symbols in SortSet are Sorts. Maybe.
-- | True iff the argument is a legal 'Sign'ature.
isLegal :: Sign -> Bool
isLegal sign = let
    has'sort sort = Set.member (asSort sort) (sorts sign)
    has'subsorts = Fold.all has'sort . getSorts $ subsorts sign
    has'ops = Fold.all has'sort . getSorts $ ops sign
    in all id [has'subsorts, has'ops]

-- | True iff the first argument is a subsignature of the second.
isSubsign :: Sign -> Sign -> Bool
isSubsign sig1 sig2 = let
    apply func items = func (items sig1) (items sig2)
    has'sorts = apply Set.isSubsetOf sorts
    has'subsorts = apply Rel.isSubrelOf subsorts
    has'ops = apply Map.isSubmapOf ops
    in all id [has'sorts, has'subsorts, has'ops]

-- | True if the given 'Sign'ature can include the given 'Sentence'.
includesSentence :: Sign -> Sentence -> Bool
includesSentence sign sen = let
    apply func a1 a2 = func (a1 sen) (a2 sign)
    has'ops   = apply Set.isSubsetOf getOps getOps
    has'sorts = apply Set.isSubsetOf getSorts getSorts
    in all id [has'sorts, has'ops]

-- * Modification

-- TODO: Add real implementation of simplification. Maybe.
-- | Simplification of sentences (leave out qualifications)
simplifySentence :: Sign -> Sentence -> Sentence
simplifySentence _ = id

-- | Rename the given 'Sort' in the given 'Sign'ature.
renameSort :: Symbol -> Symbol -> Sign -> Sign
renameSort from to = mapSorts $ Map.singleton from to

-- | Rename the given 'Label' in the given 'Sign'ature.
renameLabel :: Symbol -> Symbol -> Sign -> Sign
renameLabel from to = mapLabels $ Map.singleton from to

-- | Rename the given 'Operator' in the given 'Sign'ature.
renameOp :: Symbol -> Symbol -> [Attr] -> Sign -> Sign
renameOp from to attrs sign = let
    subrel = subsorts sign
    opmap = ops sign
    mapped = mapOpDecl subrel from to attrs opmap
    in sign { ops = mapped }
