{- |
Module      :  $Header$
Description :  Morphisms for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Morphism (
    Morphism(..),
    fromSignRenamings,
    fromSignsRenamings,
    symbolMap,
    empty,
    identity,
    isIdentity,
    createInclMorph,
    inverse,
    compose,
    isLegal,
    isInclusion,
    mapSentence,
    renameSorts,
    union,
    setTarget,
    extendMorphismSorts,
    addQualification
) where

import Maude.AS_Maude
import Maude.Symbol
import Maude.Sentence
import Maude.Meta
import Maude.Util
import Maude.Printing
import Maude.Sign (Sign)
import qualified Maude.Sign as Sign

import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Result (Result)
import qualified Common.Result as Result

import Common.Doc as Doc hiding (empty)
import Common.DocUtils
import Common.Id (mkSimpleId)

import Data.Maybe

type Profile = ([Qid], Qid)
type QidMap = Map.Map Qid Qid
type SortMap = QidMap
type OpMap = Map.Map Qid (Map.Map Profile (Qid, Profile))
type LabelMap = QidMap

data Morphism = Morphism {
        source :: Sign,
        target :: Sign,
        sortMap :: SortMap,
        opMap :: OpMap,
        labelMap :: LabelMap
    } deriving (Show, Ord, Eq)

instance Pretty Morphism where
  pretty m = Doc.text $ printMorphism (sortMap m) (opMap m) (labelMap m)
                        ++ "\n\nTarget:\n" ++ printSign (Sign.sorts sign) 
                        (Sign.subsorts sign) (Sign.ops sign)
      where sign = target m

-- | create a Morphism from an initial signature and a list of Renamings
fromSignRenamings :: Sign -> [Renaming] -> Morphism
fromSignRenamings sg rnms = applyRenamings (createInclMorph sg sg) rnms

applyRenamings :: Morphism -> [Renaming] -> Morphism
applyRenamings m rnms = foldr applyRenaming2 (foldr applyRenaming1 m rnms) rnms

-- | Rename the signature with the operator renaming and creates a morphism
-- with only the operator map. Sort renamings have to be applied to this
-- morphism.
applyRenaming1 :: Renaming -> Morphism -> Morphism
applyRenaming1 rnm mor = let
        tgt = target mor
        omap = opMap mor
    in case rnm of
        OpRenaming1 from (To to ats) -> let
                a = getName from
                b = getName to
            in mor {
                target = Sign.renameOp a b ats tgt,
                opMap = allProfilesRenaming a b tgt omap
            }
        OpRenaming2 from ar co (To to ats) -> let
                a = getName from
                b = getName to
                ar' = map getName ar
                co' = getName co
                p = (ar', co')
            in mor {
                target = Sign.renameOpProfile a ar' b ats tgt,
                opMap = Map.insertWith (Map.union) a (Map.insert p (b, p) Map.empty) omap
            }
        _ -> mor

-- | Rename a signature with the sort and label renamings, and modify
-- the given morphism by renaming the sorts in the profiles.
applyRenaming2 :: Renaming -> Morphism -> Morphism
applyRenaming2 rnm mor = let
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
    in case rnm of
        SortRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                target = Sign.renameSort a b tgt,
                sortMap = Map.insert a b smap,
                opMap = renameSortOpMap a b omap
            }
        LabelRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                labelMap = Map.insert a b lmap
            }
        _ -> mor

-- | Rename sorts in the profiles of an operator map.
renameSortOpMap :: Qid -> Qid -> OpMap -> OpMap
renameSortOpMap from to = Map.map f
          where f = \ x -> Map.map g x
                       where g = \ (q, (ar, co)) -> (q, (map h ar, if co == from
                                                                   then to
                                                                   else co))
                                         where h = \ x -> if x == from
                                                          then to
                                                          else x

allProfilesRenaming :: Qid -> Qid -> Sign -> OpMap -> OpMap
allProfilesRenaming from to sg om = om'
           where om_sg = Sign.ops sg
                 om' = if Map.member from om_sg
                       then Map.insert from (allProfilesRenamingAux to $ fromJust $ Map.lookup from om_sg) om
                       else om

allProfilesRenamingAux :: Qid -> Sign.OpDeclSet -> Map.Map Profile (Qid, Profile)
allProfilesRenamingAux q = Set.fold (f q) Map.empty
           where f = \ to (x, y, _) m -> Map.insert (x, y) (to, (x, y)) m

-- | extract a Symbol Map from a Morphism
symbolMap :: Morphism -> SymbolMap
symbolMap mor = Map.unions [(sortMap2symbolMap $ sortMap mor),
                            (opMap2symbolMap $ opMap mor),
                            (labelMap2symbolMap $ labelMap mor)]

sortMap2symbolMap :: QidMap -> SymbolMap
sortMap2symbolMap = Map.fromList . map f . Map.toList
           where f = \ (x, y) -> (Sort x, Sort y)

opMap2symbolMap :: OpMap -> SymbolMap
opMap2symbolMap = Map.fromList . map (h . f) . Map.toList
           where f = \ (x, y) -> map (g x) $ Map.toList y
                       where g = \ q1 ((ar1, co1), (q2, (ar2, co2))) -> 
                                      (Operator q1 ar1 co1, Operator q2 ar2 co2)
                 h = \ [a] -> a

-- type OpMap = Map.Map Qid (Map.Map Profile (Qid, Profile))

labelMap2symbolMap :: QidMap -> SymbolMap
labelMap2symbolMap = Map.fromList . map f . Map.toList
           where f = \ (x, y) -> (Lab x, Lab y)

-- | create a Morphism from the initial signatures and a list of Renamings
fromSignsRenamings :: Sign -> Sign -> [Renaming] -> Morphism
fromSignsRenamings sg1 sg2 rnms = foldr insertRenaming2 (foldr insertRenaming1 m rnms) rnms
           where m = createInclMorph sg1 sg2

-- | insert a Renaming into a Morphism
insertRenaming1 :: Renaming -> Morphism -> Morphism
insertRenaming1 rename mor = let
        tgt = target mor
        omap = opMap mor
    in case rename of
        OpRenaming1 from (To to _) -> let
                a = getName from
                b = getName to
            in mor {
                opMap = allProfilesRenaming a b tgt omap
            }
        OpRenaming2 from ar co (To to _) -> let
                a = getName from
                b = getName to
                ar' = map getName ar
                co' = getName co
                p = (ar', co')
            in mor {
                opMap = Map.insertWith (Map.union) a (Map.insert p (b, p) Map.empty) omap
            }
        _ -> mor

insertRenaming2 :: Renaming -> Morphism -> Morphism
insertRenaming2 rename mor = let
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
    in case rename of
        SortRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                sortMap = Map.insert a b smap,
                opMap = renameSortOpMap a b omap
            }
        LabelRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                labelMap = Map.insert a b lmap
            }
        _ -> mor

-- | the empty Morphism
empty :: Morphism
empty = identity Sign.empty

-- | the identity Morphism
identity :: Sign -> Morphism
identity sign = createInclMorph sign sign

isIdentity :: Morphism -> Bool
isIdentity m = source m == target m

-- | the inclusion Morphism
createInclMorph :: Sign -> Sign -> Morphism
createInclMorph src tgt = Morphism {
        source = src,
        target = tgt,
        sortMap = Map.empty,
        opMap = Map.empty,
        labelMap = Map.empty
    }

-- | the inverse Morphism
inverse :: Morphism -> Result Morphism
inverse mor = let
        inverseMap = Map.foldWithKey (flip Map.insert) Map.empty
    in return Morphism {
        source = (target mor),
        target = (source mor),
        sortMap  = inverseMap (sortMap mor),
        opMap    = inverseOpMap (opMap mor),
        labelMap = inverseMap (labelMap mor)
    }

inverseOpMap :: OpMap -> OpMap
inverseOpMap om = om'
    where l = createList om
          om' = createOpMapFromList l

-- type Profile = ([Qid], Qid)
-- type OpMap = Map.Map Qid (Map.Map Profile (Qid, Profile))

createList :: OpMap -> [(Qid, Profile, Qid, Profile)]
createList = map (h . f) . Map.toList
           where f = \ (x, y) -> map (g x) $ Map.toList y
                       where g = \ q1 ((ar1, co1), (q2, (ar2, co2))) -> 
                                      (q1, (ar1, co1), q2, (ar2, co2))
                 h = \ [a] -> a

createOpMapFromList :: [(Qid, Profile, Qid, Profile)] -> OpMap
createOpMapFromList = foldr f Map.empty
           where f = \ (q1, p1, q2, p2) m -> 
                           Map.insertWith (Map.union) q2 (Map.insert p2 (q1, p1) Map.empty) m

-- | the composition of two Morphisms
-- TODO: Ops don't have labels, so Signs don't have labels. so we can ignore the labelMap. Is that correct?
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
        in return (createInclMorph (source f) $ target g) {
                sortMap = compose'map sortMap getSorts -- ,
                -- opMap = compose'map opMap getOps -- ,
                -- labelMap = compose'map labelMap getLabels
            }

-- | check that a Morphism is legal
-- TODO: Ops don't have labels, so Signs don't have labels. so we can ignore the labelMap. Is that correct?
isLegal :: Morphism -> Bool
isLegal mor = let
        src = source mor
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        -- lmap = labelMap mor
        subset mp items = Set.isSubsetOf (Set.map (mapAsFunction mp) $ items src) (items tgt)
        legal'source = Sign.isLegal src
        legal'sortMap = subset smap getSorts
        -- legal'opMap = subset omap getOps
        legal'opMap = True
        -- legal'labelMap = subset lmap getLabels
        legal'labelMap = True
        legal'target = Sign.isLegal tgt
    in all id [legal'source, legal'sortMap, legal'opMap, legal'labelMap, legal'target]

-- | check that a Morphism is an Inclusion
isInclusion :: Morphism -> Bool
-- TODO: Implement Morphism.isInclusion.
isInclusion mor = let
        null'sortMap  = Map.null (sortMap mor)
        null'opMap    = Map.null (opMap mor)
        null'labelMap = Map.null (labelMap mor)
    in all id [null'sortMap, null'opMap, null'labelMap]

-- | translate a Sentence along a Morphism
mapSentence :: Morphism -> Sentence -> Result Sentence
mapSentence mor = let
        smap = mapSorts (sortMap mor)
--        omap = mapOps (opMap mor)
        lmap = mapLabels (labelMap mor)
    in return . lmap . smap -- . omap . smap

union :: Morphism -> Morphism -> Morphism
union m1 m2 = Morphism {
        source = Sign.union (source m1) $ source m2,
        target = Sign.union (target m1) $ target m2,
        sortMap = Map.union (sortMap m1) $ sortMap m2,
        opMap = Map.unionWith (Map.union) (opMap m1) $ opMap m2,
        labelMap = Map.union (labelMap m1) $ labelMap m2
    }

setTarget :: Sign -> Morphism -> Morphism
setTarget sg morph = morph {target = sg}

renameSorts :: Morphism -> [Qid] -> [Qid]
renameSorts m = map f
    where sm = sortMap m
          f = \ x -> if Map.member x sm
                     then fromJust $ Map.lookup x sm
                     else x

extendMorphismSorts :: Morphism -> Qid -> [Qid] -> Morphism
extendMorphismSorts mor sym syms = let
       tgt = target mor
       smap = sortMap mor
     in mor {
           target = Sign.renameListSort (createRenaming sym syms) tgt,
           sortMap = extendSortMap sym syms smap
        }

createRenaming :: Qid -> [Qid] -> [(Qid, Qid)]
createRenaming _ [] = []
createRenaming sym (sym' : syms) = (sym', new_sym) : createRenaming sym syms
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'

extendSortMap :: Qid -> [Qid] -> QidMap -> QidMap
extendSortMap _ [] sm = sm
extendSortMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
             sort_map' = Map.fromList $ extendSortList sym' new_sym $ Map.toList sort_map

extendSortList :: Qid -> Qid -> [(Qid, Qid)] -> [(Qid, Qid)]
extendSortList from to [] = [(from, to)]
extendSortList from to (s@(sym1, sym2) : syms) = if from == sym2
                                               then (sym1, to) : syms
                                               else s : extendSortList from to syms

addQualification :: Morphism -> Qid -> [Qid] -> Morphism
addQualification mor sym syms = let
       src = source mor
       smap = sortMap mor
     in mor {
           source = Sign.renameListSort (createRenaming sym syms) src,
           sortMap = qualifyMap sym syms smap
        }

qualifyMap :: Qid -> [Qid] -> QidMap -> QidMap
qualifyMap _ [] sm = sm
qualifyMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
             sort_map' = Map.fromList $ qualifySortList sym' new_sym $ Map.toList sort_map

qualifySortList :: Qid -> Qid -> [(Qid, Qid)] -> [(Qid, Qid)]
qualifySortList from to [] = [(from, to)]
qualifySortList from to (s@(sym1, sym2) : syms) = if from == sym1
                                                  then (to, sym2) : syms
                                                  else s : qualifySortList from to syms

-- | TODO :
-- - compose with the new OpMap
-- - isLegal with the new OpMap
-- - mapSentence with the new OpMap
-- - inverseOpMap (Adrian)

