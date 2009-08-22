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
    -- fromSignRenamings,
    -- applyRenamings,
    -- fromSignsRenamings,
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
    -- getNewSorts,
) where

-- import Maude.AS_Maude
import Maude.Symbol
import Maude.Meta
import Maude.Util
import Maude.Printing ()

import Maude.Sign (Sign)
import Maude.Sentence (Sentence)
import qualified Maude.Sign as Sign
import qualified Maude.Sentence as Sen

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

-- -- | create a Morphism from an initial signature and a list of Renamings
-- fromSignRenamings :: Sign -> [Renaming] -> Morphism
-- fromSignRenamings sg rnms = applyRenamings (createInclMorph sg sg) rnms
-- 
-- applyRenamings :: Morphism -> [Renaming] -> Morphism
-- applyRenamings m rnms = foldr applyRenaming2 (foldr applyRenaming1 m rnms) rnms
-- 
-- -- | Rename the signature with the operator renaming and creates a morphism
-- -- with only the operator map. Sort renamings have to be applied to this
-- -- morphism.
-- applyRenaming1 :: Renaming -> Morphism -> Morphism
-- applyRenaming1 rnm mor = let
--         tgt = target mor
--         omap = opMap mor
--     in case rnm of
--         OpRenaming1 from (To to ats) -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 target = Sign.renameOp a b ats tgt,
--                 opMap = allProfilesRenaming a b tgt omap
--             }
--         OpRenaming2 from ar co (To to ats) -> let
--                 a = getName from
--                 b = getName to
--                 ar' = map getName ar
--                 co' = getName co
--                 p = (ar', co')
--             in mor {
--                 target = Sign.renameOpProfile a ar' b ats tgt,
--                 opMap = Map.insertWith (Map.union) a (Map.insert p (b, p) Map.empty) omap
--             }
--         _ -> mor
-- 
-- -- | Rename a signature with the sort and label renamings, and modify
-- -- the given morphism by renaming the sorts in the profiles.
-- applyRenaming2 :: Renaming -> Morphism -> Morphism
-- applyRenaming2 rnm mor = let
--         tgt = target mor
--         smap = sortMap mor
--         omap = opMap mor
--         lmap = labelMap mor
--     in case rnm of
--         SortRenaming from to -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 target = Sign.renameSort a b tgt,
--                 sortMap = Map.insert a b smap,
--                 opMap = renameSortOpMap a b omap
--             }
--         LabelRenaming from to -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 target = Sign.renameLabel a b tgt,
--                 labelMap = Map.insert a b lmap
--             }
--         _ -> mor

-- -- | Rename sorts in the profiles of an operator map.
-- renameSortOpMap :: Qid -> Qid -> OpMap -> OpMap
-- renameSortOpMap from to = Map.map f
--           where f = \ x -> Map.map g x
--                        where g = \ (q, (ar, co)) -> (q, (map h ar, if co == from
--                                                                    then to
--                                                                    else co))
--                                          where h = \ x -> if x == from
--                                                           then to
--                                                           else x
-- 
-- allProfilesRenaming :: Qid -> Qid -> Sign -> OpMap -> OpMap
-- allProfilesRenaming from to sg om = om'
--            where om_sg = Sign.ops sg
--                  om' = if Map.member from om_sg
--                        then Map.insert from (allProfilesRenamingAux to $ fromJust $ Map.lookup from om_sg) om
--                        else om
-- 
-- allProfilesRenamingAux :: Qid -> Sign.OpDeclSet -> Map.Map Profile (Qid, Profile)
-- allProfilesRenamingAux q = Set.fold (f q) Map.empty
--            where f = \ to (x, y, _) m -> Map.insert (x, y) (to, (x, y)) m

-- -- | create a Morphism from the initial signatures and a list of Renamings
-- fromSignsRenamings :: Sign -> Sign -> [Renaming] -> Morphism
-- fromSignsRenamings sg1 sg2 rnms = foldr insertRenaming2 (foldr insertRenaming1 m rnms) rnms
--            where m = createInclMorph sg1 sg2
-- 
-- -- | insert a Renaming into a Morphism
-- insertRenaming1 :: Renaming -> Morphism -> Morphism
-- insertRenaming1 rename mor = let
--         tgt = target mor
--         omap = opMap mor
--     in case rename of
--         OpRenaming1 from (To to _) -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 opMap = allProfilesRenaming a b tgt omap
--             }
--         OpRenaming2 from ar co (To to _) -> let
--                 a = getName from
--                 b = getName to
--                 ar' = map getName ar
--                 co' = getName co
--                 p = (ar', co')
--             in mor {
--                 opMap = Map.insertWith (Map.union) a (Map.insert p (b, p) Map.empty) omap
--             }
--         _ -> mor
-- 
-- insertRenaming2 :: Renaming -> Morphism -> Morphism
-- insertRenaming2 rename mor = let
--         smap = sortMap mor
--         omap = opMap mor
--         lmap = labelMap mor
--     in case rename of
--         SortRenaming from to -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 sortMap = Map.insert a b smap,
--                 opMap = renameSortOpMap a b omap
--             }
--         LabelRenaming from to -> let
--                 a = getName from
--                 b = getName to
--             in mor {
--                 labelMap = Map.insert a b lmap
--             }
--         _ -> mor

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
    | target f /= source g = fail "target of the first and source of the second morphism are different"
    | otherwise = let
            -- map'map takes:
            --   mp :: Morphism -> SymbolMap
            -- and returns a function |Symbol -> Symbol|
            -- by treating each SymbolMap as a function and then combining them
            map'map mp = mapAsFunction (mp g) . mapAsFunction (mp f)
            -- insert takes:
            --   mp :: Morphism -> SymbolMap
            --   x :: Symbol
            -- and returns a funcion |SymbolMap -> SymbolMap|
            -- by applying both SymbolMaps (from |f| and |g|) to |x|, then
            -- inserting the resulting renaming into the SymbolMap if there is one
            -- and just leaving it (the SymbolMap) alone otherwise.
            insert mp x = let y = map'map mp x
                in if x == y then id else Map.insert x y
            -- compose'map takes:
            --   mp :: Morphism -> SymbolMap
            --   items :: Sign -> SymbolSet
            -- and constructs a combined SymbolMap from both our Morphisms
            compose'map mp items = if Map.null (mp g)
                -- if the SymbolMap of |g| is empty, we just use the one from |f|
                then mp f
                -- otherwise we start with the SymbolSet from |source f|
                -- and construct a combined SymbolMap by applying both
                -- SymbolMaps (from |f| and |g|) to each item in |insert|
                else Set.fold (insert mp) Map.empty $ items (source f)
        -- We want a morphism from |source f| to |target g|,
        in return (inclusion (source f) $ target g) {
                sortMap = compose'map sortMap getSorts -- ,
                -- opMap = compose'map opMap getOps -- ,
                -- labelMap = compose'map labelMap getLabels
            }

-- | check that a Morphism is legal
isLegal :: Morphism -> Bool
isLegal mor = let
        src = source mor
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
        subset mp items = Set.isSubsetOf (Set.map (mapAsFunction mp) $ items src) (items tgt)
        legal'source = Sign.isLegal src
        legal'sortMap = subset smap getSorts
        legal'opMap = subset omap getOps
        legal'labelMap = subset lmap getLabels
        legal'target = Sign.isLegal tgt
    in all id [legal'source, legal'sortMap, legal'opMap, legal'labelMap, legal'target]

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
-- TODO: Restore mapSentence once we get mapOps working.
mapSentence mor = let
        smap = mapSorts (sortMap mor)
        -- omap = mapOps (opMap mor)
        lmap = mapLabels (labelMap mor)
    in return . lmap . smap
    -- in return . lmap . omap . smap

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
-- 
-- extendSortMap :: Qid -> [Qid] -> QidMap -> QidMap
-- extendSortMap _ [] sm = sm
-- extendSortMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
--        where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
--              sort_map' = Map.fromList $ extendSortList sym' new_sym $ Map.toList sort_map
-- 
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

-- getNewSorts :: [Qid] -> Morphism -> [Qid]
-- getNewSorts ss morph = getNewSortsSortMap ss (sortMap morph)
-- 
-- getNewSortsSortMap :: [Qid] -> QidMap -> [Qid]
-- getNewSortsSortMap [] _ = []
-- getNewSortsSortMap (s : ss) qm = s' : getNewSortsSortMap ss qm
--               where s' = if Map.member s qm
--                          then fromJust $ Map.lookup s qm
--                          else s

-- | TODO :
-- - compose with the new OpMap
-- - isLegal with the new OpMap
-- - mapSentence with the new OpMap
