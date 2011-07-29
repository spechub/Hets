{- |
Module      :  $Header$
Description :  Maude Morphisms
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for Maude.
-}

module Maude.Morphism (
    -- * Types

    -- ** The Morphism type
    Morphism (..),
    -- ** Auxiliary type
    SortMap,
    KindMap,
    OpMap,
    -- * Construction
    fromSignRenamings,
    fromSignsRenamings,
    empty,
    identity,
    inclusion,
    -- * Combination
    inverse,
    union,
    compose,
    -- * Testing
    isInclusion,
    isLegal,
    -- * Conversion
    symbolMap,
    -- * Modification
    setTarget,
    qualifySorts,
    applyRenamings,
    extendWithSortRenaming,
    -- * Application
    translateSentence,
    translateSorts,
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta
import Maude.Util
import Maude.Printing ()

import Maude.Sign (Sign, kindRel, KindRel)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign

import Data.List (partition)
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Result (Result)

import Common.Doc hiding (empty)
import Common.DocUtils (Pretty (..))

-- * Types

-- ** Auxiliary types

type SortMap = SymbolMap
type KindMap = SymbolMap
type OpMap = SymbolMap
type LabelMap = SymbolMap

-- ** The Morphism type

data Morphism = Morphism {
        source :: Sign,
        target :: Sign,
        sortMap :: SortMap,
        kindMap :: KindMap,
        opMap :: OpMap,
        labelMap :: LabelMap
    } deriving (Show, Ord, Eq)

-- ** 'Morphism' instances

instance Pretty Morphism where
    pretty mor = let
        pr'pair txt left right = hsep
            [txt, pretty left, text "to", pretty right]
        pr'ops src tgt = pr'pair (text "op") src (getName tgt)
        pr'map fun = vcat . map (uncurry fun) . Map.toList
        smap = pr'map (pr'pair $ text "sort") $ sortMap mor
        kmap = pr'map (pr'pair $ text "kind") $ kindMap mor
        omap = pr'map pr'ops $ opMap mor
        lmap = pr'map (pr'pair $ text "label") $ labelMap mor
        s = pretty $ source mor
        t = pretty $ target mor
        in vcat [ smap, kmap, omap, lmap, pretty "\nSource:\n", s
                , pretty "\nTarget\n", t ]

-- * Helper functions

-- ** to modify Morphisms

mapTarget :: (Sign -> Sign) -> Morphism -> Morphism
mapTarget func mor = mor { target = func $ target mor }

mapSortMap :: (SortMap -> SortMap) -> Morphism -> Morphism
mapSortMap func mor = mor { sortMap = func $ sortMap mor }
mapOpMap :: (OpMap -> OpMap) -> Morphism -> Morphism
mapOpMap func mor = mor { opMap = func $ opMap mor }
mapLabelMap :: (LabelMap -> LabelMap) -> Morphism -> Morphism
mapLabelMap func mor = mor { labelMap = func $ labelMap mor }

-- ** to handle Renamings

-- TODO: Handle Attrs in Op Renamings.
renamingSymbolsMaybe :: Renaming -> Maybe (Symbol, Symbol)
renamingSymbolsMaybe rename = case rename of
    SortRenaming src tgt -> Just (asSymbol src, asSymbol tgt)
    LabelRenaming src tgt -> Just (asSymbol src, asSymbol tgt)
    OpRenaming1 src (To tgt _) -> Just (asSymbol src, asSymbol tgt)
    OpRenaming2 src dom cod (To tgt _) -> let
        src' = Op src dom cod []
        tgt' = Op tgt dom cod []
        in Just (asSymbol src', asSymbol tgt')
    TermMap _ _ -> Nothing

-- | Extract the 'Symbol's from a 'Renaming', if possible.
renamingSymbols :: Renaming -> (Symbol, Symbol)
renamingSymbols = fromJust . renamingSymbolsMaybe

-- | Separate Operator and other Renamings.
partitionRenamings :: [Renaming] -> ([Renaming], [Renaming])
partitionRenamings = let
    is'op renaming = case renaming of
        OpRenaming1 _ _ -> True
        OpRenaming2 _ _ _ _ -> True
        _ -> False
    in partition is'op

-- ** to apply Renamings to Morphisms

{- | Insert an 'Operator' 'Renaming' into a 'Morphism'.
Iff apply is True, apply the Renaming to the Morphism's target Signature. -}
insertOpRenaming :: Bool -> Renaming -> Morphism -> Morphism
insertOpRenaming apply rename = let
    syms = renamingSymbols rename
    add'op = mapOpMap $ uncurry Map.insert syms
    use'op attrs = if apply
        then mapTarget $ uncurry Sign.renameOp syms attrs
        else id
    in case rename of
        OpRenaming1 _ (To _ attrs) -> use'op attrs . add'op
        OpRenaming2 _ _ _ (To _ attrs) -> use'op attrs . add'op
        _ -> id

{- | Insert a non-Operator 'Renaming' into a 'Morphism'.
iff True, apply the Renaming to the target Sign -}
insertRenaming :: Bool -> Renaming -> Morphism -> Morphism
insertRenaming apply rename = let
    syms = renamingSymbols rename
    add'sort = mapSortMap $ uncurry Map.insert syms
    use'sort = if apply
        then mapTarget $ uncurry Sign.renameSort syms
        else id
    ren'sort = mapOpMap $ uncurry renameSortOpMap syms
    add'labl = mapLabelMap $ uncurry Map.insert syms
    use'labl = if apply
        then mapTarget $ uncurry Sign.renameLabel syms
        else id
    in case rename of
        SortRenaming _ _ -> ren'sort . use'sort . add'sort
        LabelRenaming _ _ -> use'labl . add'labl
        _ -> id

-- | Rename sorts in the profiles of an operator map.
renameSortOpMap :: Symbol -> Symbol -> OpMap -> OpMap
renameSortOpMap from to = Map.map $ mapSorts $ Map.singleton from to

-- | Insert 'Renaming's into a 'Morphism'.
insertRenamings :: Bool -> Morphism -> [Renaming] -> Morphism
insertRenamings apply mor rens = let
    (ops, rest) = partitionRenamings rens
    add'ops = flip (foldr $ insertOpRenaming apply) ops
    add'rest = flip (foldr $ insertRenaming apply) rest
    in add'rest . add'ops $ mor

-- * Construction

-- | Create a 'Morphism' from an initial 'Sign'ature and a list of 'Renaming's.
fromSignRenamings :: Sign -> [Renaming] -> Morphism
fromSignRenamings s rs = kindMorph $ insertRenamings True (identity s) rs

-- | Create a 'Morphism' from a pair of 'Sign'atures and a list of 'Renaming's.
fromSignsRenamings :: Sign -> Sign -> [Renaming] -> Morphism
fromSignsRenamings sign1 sign2 rs =
  kindMorph $ insertRenamings False (inclusion sign1 sign2) rs

-- | the empty 'Morphism'
empty :: Morphism
empty = identity Sign.empty

-- | the identity 'Morphism'
identity :: Sign -> Morphism
identity sign = inclusion sign sign

-- | the inclusion 'Morphism'
inclusion :: Sign -> Sign -> Morphism
inclusion src tgt = Morphism {
        source = src,
        target = tgt,
        sortMap = Map.empty,
        kindMap = Map.empty,
        opMap = Map.empty,
        labelMap = Map.empty
    }

-- * Combination

-- | the inverse 'Morphism'
inverse :: Morphism -> Result Morphism
inverse mor = let
    invertMap = Map.foldWithKey (flip Map.insert) Map.empty
    in return $ kindMorph Morphism {
        source = target mor,
        target = source mor,
        sortMap = invertMap $ sortMap mor,
        kindMap = invertMap $ kindMap mor,
        opMap = invertMap $ opMap mor,
        labelMap = invertMap $ labelMap mor
    }

-- | the union of two 'Morphism's
union :: Morphism -> Morphism -> Morphism
union mor1 mor2 = let
    apply func items = func (items mor1) (items mor2)
    in kindMorph Morphism {
        source = apply Sign.union source,
        target = apply Sign.union target,
        sortMap = apply Map.union sortMap,
        kindMap = apply Map.union kindMap,
        opMap = apply Map.union opMap,
        labelMap = apply Map.union labelMap
    }

-- Just a shorthand for types inside compose.
type Extraction = Morphism -> SymbolMap

-- | the composition of two 'Morphism's
compose :: Morphism -> Morphism -> Result Morphism
compose f g
    | target f /= source g = fail
        "target of the first and source of the second morphism are different"
    | otherwise = let
        {- Take SymbolMap |mp| of each Morphism.
        Convert each SymbolMap to a function.
        Compose those functions. -}
        map'map :: Extraction -> Symbol -> Symbol
        map'map mp = mapAsFunction (mp g) . mapAsFunction (mp f)
        {- Map |x| via the composed SymbolMaps |mp| of both Morphisms.
        Insert the renaming mapping into a SymbolMap. -}
        insert :: Extraction -> Symbol -> SymbolMap -> SymbolMap
        insert mp x = let y = map'map mp x
            in if x == y then id else Map.insert x y
        -- Map each symbol in |items| via the combined SymbolMaps |mp|.
        compose'map :: Extraction -> (Sign -> SymbolSet) -> SymbolMap
        compose'map mp items = if Map.null (mp g)
            -- if the SymbolMap of |g| is empty, we use the one from |f|
            then mp f
            {- otherwise we start with the SymbolSet from |source f|
            and construct a combined SymbolMap by applying both
            SymbolMaps (from |f| and |g|) to each item in |insert| -}
            else Set.fold (insert mp) Map.empty $ items (source f)
        -- We want a morphism from |source f| to |target g|.
        mor = inclusion (source f) (target g)
        in return $ kindMorph mor {
            sortMap = compose'map sortMap getSorts,
            opMap = compose'map opMap getOps,
            labelMap = compose'map labelMap getLabels
        }

-- * Testing

-- | True iff the 'Morphism' is an inclusion
isInclusion :: Morphism -> Bool
isInclusion mor = let
    null'sortMap = Map.null (sortMap mor)
    null'opMap = Map.null (opMap mor)
    null'labelMap = Map.null (labelMap mor)
    in all id [null'sortMap, null'opMap, null'labelMap]

-- | True iff the 'Morphism' is legal
isLegal :: Morphism -> Result ()
isLegal mor = let
    src = source mor
    tgt = target mor
    smap = sortMap mor
    omap = opMap mor
    lmap = labelMap mor
    subset mp items = let mapped = Set.map $ mapAsFunction mp
        in Set.isSubsetOf (mapped $ items src) $ items tgt
    lg'source = Sign.isLegal src
    lg'sortMap = subset smap getSorts
    lg'opMap = subset omap getOps
    lg'labelMap = subset lmap getLabels
    lg'target = Sign.isLegal tgt
    in if all id [lg'source, lg'sortMap, lg'opMap, lg'labelMap, lg'target]
    then return () else fail "illegal Maude morphism"

-- * Conversion

-- | extract the complete 'SymbolMap' of a 'Morphism'
symbolMap :: Morphism -> SymbolMap
symbolMap mor = Map.unions [sortMap mor, opMap mor, labelMap mor]

-- * Modification

-- | set a new target for a 'Morphism'
setTarget :: Sign -> Morphism -> Morphism
setTarget sg m = kindMorph $ mapTarget (const sg) m

-- | qualify a list of 'Symbol's inside a 'Morphism'
qualifySorts :: Morphism -> Qid -> Symbols -> Morphism
qualifySorts mor qid syms = let
    insert symb = Map.insert symb $ qualify qid symb
    smap = foldr insert Map.empty syms
    q'tgt = mapTarget $ mapSorts smap
    q'smap = mapSortMap $ mapSorts smap
    x'smap = mapSortMap $ Map.union smap
    in kindMorph $ q'tgt . x'smap . q'smap $ mor

-- | apply a list of 'Renaming's to a 'Morphism'
applyRenamings :: Morphism -> [Renaming] -> Morphism
applyRenamings m rs = kindMorph $ insertRenamings True m rs

-- | apply a 'Sort' 'Renaming' to a 'Morphism'
extendWithSortRenaming :: Symbol -> Symbol -> Morphism -> Morphism
extendWithSortRenaming src tgt m = let
    add'sort = mapSortMap $ Map.insert src tgt
    use'sort = mapTarget $ Sign.renameSort src tgt
    ren'sort = mapOpMap $ renameSortOpMap src tgt
    in kindMorph $ ren'sort . use'sort $ add'sort m

-- * Application

-- | translate a 'Sentence' along a 'Morphism'
translateSentence :: Morphism -> Sentence -> Result Sentence
translateSentence mor = let
    smap = mapSorts (sortMap mor)
    omap = mapOps (opMap mor)
    lmap = mapLabels (labelMap mor)
    in return . lmap . smap . omap

-- | translate 'Sort's along a 'Morphism'
translateSorts :: (HasSorts a) => Morphism -> a -> a
translateSorts = mapSorts . sortMap

-- * Auxiliary functions
kindMorph :: Morphism -> Morphism
kindMorph morph = morph { kindMap = kindMorphAux kr1 sm kr2}
     where kr1 = kindRel $ source morph
           kr2 = kindRel $ target morph
           sm = Map.toList $ sortMap morph

kindMorphAux :: KindRel -> [(Symbol, Symbol)] -> KindRel -> KindMap
kindMorphAux _ [] _ = Map.empty
kindMorphAux kr1 ((s1, s2) : ls) kr2 = Map.union m m'
     where m = kindMorphAux kr1 ls kr2
           (k1, k2) = case (Map.lookup s1 kr1, Map.lookup s2 kr2) of
              (Just r1, Just r2) -> (r1, r2)
              _ -> (s1, s1)
           m' = if k1 == k2
                then Map.empty
                else Map.singleton k1 k2
