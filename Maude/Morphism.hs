{- |
Module      :  $Header$
Description :  Morphisms for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for Maude.
-}

module Maude.Morphism (
    Morphism(..),
    SortMap,
    OpMap,
    applyRenamings,
    fromSignRenamings,
    fromSignsRenamings,
    symbolMap,
    empty,
    identity,
    isIdentity,
    inclusion,
    inverse,
    compose,
    isLegal,
    isInclusion,
    mapSentence,
    renameSorts,
    union,
    setTarget,
    -- extendMorphismSorts,
    -- extendWithSortRenaming,
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta
import Maude.Util
import Maude.Printing ()

import Maude.Sign (Sign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

import Data.List (partition)
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Result (Result)
import qualified Common.Result as Result

import Common.Doc hiding (empty)
import Common.DocUtils (Pretty(..))


type SortMap = SymbolMap
type OpMap = SymbolMap
type LabelMap = SymbolMap

data Morphism = Morphism {
        source :: Sign,
        target :: Sign,
        sortMap :: SortMap,
        opMap :: OpMap,
        labelMap :: LabelMap
    } deriving (Show, Ord, Eq)


instance Pretty Morphism where
    pretty mor = let
            pr'pair txt left right = hsep
                [txt, pretty left, text "to", pretty right]
            pr'ops src tgt = pr'pair (text "op") src (getName tgt)
            pr'map fun = vsep . map (uncurry fun) . Map.toList
            smap = pr'map (pr'pair $ text "sort") $ sortMap mor
            omap = pr'map pr'ops $ opMap mor
            lmap = pr'map (pr'pair $ text "label") $ labelMap mor
        in vsep [ smap, omap, lmap ]
        -- text "\n\nTarget:" <$$> pretty $ target mor


-- | Separate Operator and other Renamings.
partitionRenamings :: [Renaming] -> ([Renaming], [Renaming])
partitionRenamings = let
        is'op renaming = case renaming of
            OpRenaming1 _ _ -> True
            OpRenaming2 _ _ _ _ -> True
            _ -> False
    in partition is'op

renamingSymbolsMaybe :: Renaming -> Maybe (Symbol, Symbol)
renamingSymbolsMaybe rename = case rename of
    SortRenaming src tgt -> Just (asSymbol src, asSymbol tgt)
    LabelRenaming src tgt -> Just (asSymbol src, asSymbol tgt)
    OpRenaming1 src (To tgt _) -> Just (asSymbol src, asSymbol tgt)
    OpRenaming2 src dom cod (To tgt _) -> let
            src' = getName src
            tgt' = getName tgt
            dom' = map asSymbol dom
            cod' = asSymbol cod
        in Just (Operator src' dom' cod', Operator tgt' dom' cod')
    -- TODO: We are not currently handling TermMaps, right?
    TermMap _ _ -> Nothing

renamingSymbols :: Renaming -> (Symbol, Symbol)
renamingSymbols = fromJust . renamingSymbolsMaybe

applyRenamings :: Morphism -> [Renaming] -> Morphism
applyRenamings mor rens = let
        (ops, rest) = partitionRenamings rens
        add'ops  = flip (foldr applyOpRenaming) ops
        add'rest = flip (foldr applyRenaming) rest
    in add'rest . add'ops $ mor

-- | create a Morphism from an initial signature and a list of Renamings
fromSignRenamings :: Sign -> [Renaming] -> Morphism
fromSignRenamings = applyRenamings . identity


-- TODO: Handle Attrs in Op Renamings.
applyOpRenaming :: Renaming -> Morphism -> Morphism
applyOpRenaming rename = let
        syms = renamingSymbols rename
        add'op mor = mor { opMap = uncurry Map.insert syms $ opMap mor }
        use'op attrs mor = mor { target = uncurry Sign.renameOp syms attrs $ target mor }
    in case rename of
        OpRenaming1 _ (To _ attrs) -> use'op attrs . add'op
        OpRenaming2 _ _ _ (To _ attrs) -> use'op attrs . add'op
        _ -> id

applyRenaming :: Renaming -> Morphism -> Morphism
applyRenaming rename = let
        syms = renamingSymbols rename
        add'sort mor = mor { sortMap  = uncurry Map.insert syms $ sortMap mor }
        use'sort mor = mor { target = uncurry Sign.renameSort syms $ target mor }
        ren'sort mor = mor { opMap = uncurry renameSortOpMap syms $ opMap mor }
        add'labl mor = mor { labelMap = uncurry Map.insert syms $ labelMap mor }
        use'labl mor = mor { target = uncurry Sign.renameLabel syms $ target mor }
    in case rename of
        SortRenaming _ _ -> ren'sort . use'sort . add'sort
        LabelRenaming _ _ -> use'labl . add'labl
        _ -> id


-- | create a Morphism from the initial signatures and a list of Renamings
fromSignsRenamings :: Sign -> Sign -> [Renaming] -> Morphism
fromSignsRenamings sign1 sign2 rens = let
        (ops, rest) = partitionRenamings rens
        add'ops  = flip (foldr insertOpRenaming) ops
        add'rest = flip (foldr insertRenaming) rest
        mor = inclusion sign1 sign2
    in add'rest . add'ops $ mor

-- TODO: Handle Attrs in Op Renamings.
insertOpRenaming :: Renaming -> Morphism -> Morphism
insertOpRenaming rename = let
        syms = renamingSymbols rename
        add'op mor = mor { opMap = uncurry Map.insert syms $ opMap mor }
    in case rename of
        OpRenaming1 _ _ -> add'op
        OpRenaming2 _ _ _ _ -> add'op
        _ -> id

insertRenaming :: Renaming -> Morphism -> Morphism
insertRenaming rename = let
        syms = renamingSymbols rename
        add'sort mor = mor { sortMap  = uncurry Map.insert syms $ sortMap mor }
        ren'sort mor = mor { opMap = uncurry renameSortOpMap syms $ opMap mor }
        add'labl mor = mor { labelMap = uncurry Map.insert syms $ labelMap mor }
    in case rename of
        SortRenaming _ _ -> ren'sort . add'sort
        LabelRenaming _ _ -> add'labl
        _ -> id

-- | Rename sorts in the profiles of an operator map.
renameSortOpMap :: Symbol -> Symbol -> OpMap -> OpMap
renameSortOpMap from to = Map.map $ mapSorts $ Map.singleton from to

-- | extract the SymbolMap of a Morphism
symbolMap :: Morphism -> SymbolMap
symbolMap mor = Map.unions [sortMap mor, opMap mor, labelMap mor]

-- | the empty Morphism
empty :: Morphism
empty = identity Sign.empty

-- | the identity Morphism
identity :: Sign -> Morphism
identity sign = inclusion sign sign

-- | the inclusion Morphism
inclusion :: Sign -> Sign -> Morphism
inclusion src tgt = Morphism {
        source = src,
        target = tgt,
        sortMap = Map.empty,
        opMap = Map.empty,
        labelMap = Map.empty
    }


-- | the inverse Morphism
inverse :: Morphism -> Result Morphism
inverse mor = let
        invertMap = Map.foldWithKey (flip Map.insert) Map.empty
    in return Morphism {
        source = target mor,
        target = source mor,
        sortMap  = invertMap $ sortMap mor,
        opMap    = invertMap $ opMap mor,
        labelMap = invertMap $ labelMap mor
    }


-- | the composition of two Morphisms
compose :: Morphism -> Morphism -> Result Morphism
compose f g
    | target f /= source g = fail
        "target of the first and source of the second morphism are different"
    | otherwise = let
            -- Take SymbolMap |mp| of each Morphism.
            -- Convert each SymbolMap to a function.
            -- Compose those functions.
            map'map :: (Morphism -> SymbolMap) -> Symbol -> Symbol
            map'map mp = mapAsFunction (mp g) . mapAsFunction (mp f)
            -- Map |x| via the composed SymbolMaps |mp| of both Morphisms.
            -- Insert the renaming mapping into a SymbolMap.
            insert :: (Morphism -> SymbolMap) -> Symbol -> SymbolMap -> SymbolMap
            insert mp x = let y = map'map mp x
                in if x == y then id else Map.insert x y
            -- Map each symbol in |items| via the combined SymbolMaps |mp|.
            compose'map :: (Morphism -> SymbolMap) -> (Sign -> SymbolSet) -> SymbolMap
            compose'map mp items = if Map.null (mp g)
                -- if the SymbolMap of |g| is empty, we use the one from |f|
                then mp f
                -- otherwise we start with the SymbolSet from |source f|
                -- and construct a combined SymbolMap by applying both
                -- SymbolMaps (from |f| and |g|) to each item in |insert|
                else Set.fold (insert mp) Map.empty $ items (source f)
            -- We want a morphism from |source f| to |target g|.
            mor = inclusion (source f) (target g)
        in return mor {
                sortMap = compose'map sortMap getSorts,
                opMap = compose'map opMap getOps,
                labelMap = compose'map labelMap getLabels
            }

-- | check that a Morphism is legal
isLegal :: Morphism -> Bool
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
    in all id [lg'source, lg'sortMap, lg'opMap, lg'labelMap, lg'target]

-- | check that a Morphism is the identity
isIdentity :: Morphism -> Bool
isIdentity mor = source mor == target mor

-- | check that a Morphism is an Inclusion
isInclusion :: Morphism -> Bool
isInclusion mor = let
        null'sortMap  = Map.null (sortMap mor)
        null'opMap    = Map.null (opMap mor)
        null'labelMap = Map.null (labelMap mor)
    in all id [null'sortMap, null'opMap, null'labelMap]

-- | translate a Sentence along a Morphism
mapSentence :: Morphism -> Sentence -> Result Sentence
mapSentence mor = let
        smap = mapSorts (sortMap mor)
        omap = mapOps (opMap mor)
        lmap = mapLabels (labelMap mor)
    in return . lmap . omap . smap

union :: Morphism -> Morphism -> Morphism
union m1 m2 = let apply func items = func (items m1) (items m2)
    in Morphism {
        source = apply Sign.union source,
        target = apply Sign.union target,
        sortMap  = apply Map.union sortMap,
        opMap    = apply Map.union opMap,
        labelMap = apply Map.union labelMap
    }

setTarget :: Sign -> Morphism -> Morphism
setTarget sign morph = morph {target = sign}

renameSorts :: Morphism -> Symbols -> Symbols
renameSorts = mapSorts . sortMap

-- extendMorphismSorts :: Morphism -> Qid -> [Qid] -> Morphism
-- extendMorphismSorts mor sym syms = let
--        tgt = target mor
--        smap = sortMap mor
--      in mor {
--            target = Sign.renameListSort (createRenaming sym syms) tgt,
--            sortMap = extendSortMap sym syms smap
--         }

-- createRenaming :: Qid -> [Qid] -> [(Qid, Qid)]
-- createRenaming _ [] = []
-- createRenaming sym (sym' : syms) = (sym', new_sym) : createRenaming sym syms
--        where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'

-- extendSortMap :: Qid -> [Qid] -> QidMap -> QidMap
-- extendSortMap _ [] sm = sm
-- extendSortMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
--        where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
--              sort_map' = Map.fromList $ extendSortList sym' new_sym $ Map.toList sort_map

-- extendSortList :: Qid -> Qid -> [(Qid, Qid)] -> [(Qid, Qid)]
-- extendSortList from to [] = [(from, to)]
-- extendSortList from to (s@(sym1, sym2) : syms) = if from == sym2
--                                                then (sym1, to) : syms
--                                                else s : extendSortList from to syms

-- extendWithSortRenaming :: Qid -> Qid -> Morphism -> Morphism
-- extendWithSortRenaming from to mor = let
--         tgt = target mor
--         smap = sortMap mor
--         omap = opMap mor
--           in mor {
--                 target = Sign.renameSort from to tgt,
--                 sortMap = Map.insert from to smap,
--                 opMap = renameSortOpMap from to omap
--              }

-- | TODO :
-- - compose with the new OpMap
-- - isLegal with the new OpMap
-- - mapSentence with the new OpMap
