{-# LANGUAGE TypeSynonymInstances #-}
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
    KindRel,
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
    -- * Modification
    simplifySentence,
    renameSort,
    renameLabel,
    renameOp,
    -- * Inline printing
    inlineSign
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
import qualified Data.List as List

import Common.Doc hiding (empty)
import qualified Common.Doc as Doc
import Common.DocUtils (Pretty(..))

-- * Types

-- ** Auxiliary types

type SortSet = SymbolSet
type KindSet = SymbolSet
type SubsortRel = SymbolRel
type OpDecl = (Set Symbol, [Attr])
type OpDeclSet = Set OpDecl
type OpMap = Map Qid OpDeclSet
type Sentences = Set Sentence
type KindRel = Map Symbol Symbol

-- ** The Signature type
-- | The Signature of a Maude 'Module'.
data Sign = Sign {
        sorts :: SortSet,               -- ^ The 'Set' of 'Sort's
        kinds :: KindSet,               -- ^ The 'Set' of 'Kind's
        subsorts :: SubsortRel,         -- ^ The 'Rel'ation of 'Sort's
        ops :: OpMap,                   -- ^ The 'Map' of 'Operator's
        sentences :: Sentences,         -- ^ The 'Set' of 'Sentence's
        kindRel :: KindRel              -- ^ The 'Set' of 'Sentence's for the kind function
    } deriving (Show, Ord, Eq)

-- ** 'Sign' instances

instance Pretty Sign where
    pretty sign = let
        descend = flip . Set.fold
        -- print sort declarations
        pr'sorts ss = if null ss then Doc.empty else
            hsep [keyword "sorts", hsep $ map pretty ss, dot]
        -- print kind declarations
        pr'kinds ks = if null ks then Doc.empty else
            hsep [keyword "kinds", hsep $ map pretty ks, dot]
        -- print subsort declarations
        pr'sups = hsep . map pretty . Set.elems
        pr'pair sub sups = (:) . hsep $
            [keyword "subsort", pretty sub, less, pr'sups sups, dot]
        pr'subs = vcat . Map.foldWithKey pr'pair []
        -- print operator declarations
        pr'decl attrs symb = hsep
            [keyword "op", pretty symb, pretty attrs, dot]
        pr'ods (decls, attrs) = descend ((:) . pr'decl attrs) decls
        pr'ocs = descend pr'ods
        pr'ops = vcat . Map.fold pr'ocs []
        in vcat [ pr'sorts $ Set.elems $ sorts sign
                , pr'kinds $ Set.elems $ kinds sign
                , pr'subs $ Rel.toMap $ Rel.transReduce $ subsorts sign
                , pr'ops $ ops sign
                , pretty "op kind : Sort -> Kind ."
                , prettyPrint $ kindRel sign]
                -- NOTE: Leaving out Sentences for now.
                -- , pretty $ Set.toList $ sentences sign ]

instance HasSorts Sign where
    getSorts = sorts
    mapSorts mp sign = sign {
        sorts = mapSorts mp $ sorts sign,
        kinds = mapSorts mp $ kinds sign,
        subsorts = mapSorts mp $ subsorts sign,
        ops = mapSorts mp $ ops sign,
        kindRel = mapSorts mp $ kindRel sign
        -- NOTE: Leaving out Sentences for now.
        -- sentences = mapSorts mp $ sentences sign
    }

instance HasSorts KindRel where
    getSorts = getSortsKindRel
    mapSorts = renameSortKindRel

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
        SortStmnt sort -> (sort : sorts', subs', ops')
        SubsortStmnt sub -> (sorts', sub : subs', ops')
        OpStmnt op -> (sorts', subs', op : ops')
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
    sbs = Rel.transClosure $ subsorts sign
    kr = getkindRel (sorts sign) sbs
    in sign {
        kinds = kindsFromMap kr,
        subsorts = sbs,
        ops = addPartial $ ops sign,
        sentences = Set.fromList sents,
        kindRel = kr
    }

addPartial :: OpMap -> OpMap
addPartial om = Map.map partialODS om

partialODS :: OpDeclSet -> OpDeclSet
partialODS ods = Set.map partialSet ods

partialSet :: (Set Symbol, [Attr]) -> (Set Symbol, [Attr])
partialSet (ss, ats) = (Set.union ss ss', ats)
      where ss' = Set.map partialOp ss

partialOp :: Symbol -> Symbol
partialOp (Operator q ss s) = Operator q (map sortSym2kindSym ss) $ sortSym2kindSym s
partialOp s = s

sortSym2kindSym :: Symbol -> Symbol
sortSym2kindSym (Sort q) = Kind q
sortSym2kindSym s = s

-- | The empty 'Sign'ature.
empty :: Sign
empty = Sign {
    sorts = Set.empty,
    kinds = Set.empty,
    subsorts = Rel.empty,
    ops = Map.empty,
    sentences = Set.empty,
    kindRel = Map.empty
}

inlineSign :: Sign -> Doc
inlineSign sign = let
        descend = flip . Set.fold
        -- print sort declarations
        pr'sorts ss = if null ss then Doc.empty else
            hsep [keyword "sorts", hsep $ map pretty ss, dot]
        -- print subsort declarations
        pr'sups = hsep . map pretty . Set.elems
        pr'pair sub sups = (:) . hsep $
            [keyword "subsort", pretty sub, less, pr'sups sups, dot]
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
        attr = removeReps $ mergeAttrs attrs $ snd decl
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
        attr = removeReps $ mergeAttrs attrs $ snd decl
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

removeReps :: [Attr] -> [Attr]
removeReps [] = []
removeReps (a : as) = a : (filter (/= a) $ removeReps as)

-- * Combination

-- | The union of two 'Sign'atures.
union :: Sign -> Sign -> Sign
union sig1 sig2 = let
    apply func items = func (items sig1) (items sig2)
    kr = getkindRel (apply Set.union sorts) (apply Rel.union subsorts)
    in Sign {
        sorts = apply Set.union sorts,
        kinds = kindsFromMap kr,
        subsorts = apply Rel.union subsorts,
        ops = apply (Map.unionWith Set.union) ops,
        sentences = apply Set.union sentences,
        kindRel = kr
    }

-- | The intersection of two 'Sign'atures.
intersection :: Sign -> Sign -> Sign
intersection sig1 sig2 = let
    apply func items = func (items sig1) (items sig2)
    kr = getkindRel (apply Set.union sorts) (apply Rel.union subsorts)
    in Sign {
        sorts = apply Set.intersection sorts,
        kinds = kindsFromMap kr,
        subsorts = apply Rel.intersection subsorts,
        ops = apply Map.intersection ops,
        sentences = apply Set.intersection sentences,
        kindRel = kr
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
    has'ops = apply (Map.isSubmapOfBy subODS) ops
    in all id [has'sorts, has'subsorts, has'ops]

subODS :: OpDeclSet -> OpDeclSet -> Bool
subODS ods1 ods2 = Set.isSubsetOf ods1' ods2'
    where ods1' = removeAttsODS ods1
          ods2' = removeAttsODS ods2

removeAttsODS :: OpDeclSet -> OpDeclSet
removeAttsODS ods = Set.map removeAtts ods

removeAtts :: (Set Symbol, [Attr]) -> (Set Symbol, [Attr])
removeAtts (ss, _) = (ss, [])

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

getkindRel :: SortSet -> SubsortRel -> KindRel
getkindRel ss r = kindRelList (Set.toList ss) r Map.empty

kindRelList :: [Symbol] -> SubsortRel -> KindRel -> KindRel
kindRelList [] _ m = m
kindRelList l@(s : _) r m = kindRelList not_rel r m'
      where (top : _) = List.sort $ getTop r s
            tc = Rel.transClosure r
            (rel, not_rel) = sameKindList s tc l
            f = \ x y z -> Map.insert y (sortSym2kindSym x) z
            m' = foldr (f top) m rel

sameKindList :: Symbol -> SubsortRel -> [Symbol] -> ([Symbol], [Symbol])
sameKindList _ _ [] = ([], [])
sameKindList t r (t' : ts) = if sameKind r t t'
                       then (t' : hold, not_hold)
                       else (hold, t' : not_hold)
      where (hold, not_hold) = sameKindList t r ts

getTop :: SubsortRel -> Symbol -> [Symbol]
getTop r tok = case succs of
           [] -> [tok]
           toks@(_:_) -> foldr ((++) . (getTop r)) [] toks
      where succs = Set.toList $ Rel.succs r tok

kindsFromMap :: KindRel -> KindSet
kindsFromMap kr = foldr (\ (_,y) z -> Set.insert y z) Set.empty krl
      where krl = Map.toList kr

prettyPrint :: KindRel -> Doc
prettyPrint kr = foldr f Doc.empty krl
      where krl = Map.toList kr
            f = \ x y -> vsep [prettyKindPair x, y]

prettyKindPair :: (Symbol, Symbol) -> Doc
prettyKindPair (s, k) = hsep [keyword "eq", pretty "kind" <> (parens . pretty $ s),
                              equals, pretty k, dot]

getSortsKindRel :: KindRel -> SymbolSet
getSortsKindRel = Map.foldWithKey f Set.empty
      where f = \ k _ s -> Set.insert k s

renameSortKindRel :: Map Symbol Symbol -> KindRel -> KindRel
renameSortKindRel m kr = kr'
      where krl = Map.toList kr
            f = \ mss (x,y) z -> (mapSorts mss x, mapSorts mss y) : z
            krl' = foldr (f m) [] krl
            kr' = Map.fromList krl'
