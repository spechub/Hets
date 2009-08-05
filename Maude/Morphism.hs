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
    addQualification,
    applyMorphSign
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
  pretty m = Doc.text $ printMorphism (sortMap m) (opMap m) (labelMap m)
                        ++ "\n\nTarget:\n\n" ++ printSign (Sign.sorts sign) 
                        (Sign.subsorts sign) (Sign.ops sign)
      where sign = target m

-- | create a Morphism from an initial signature and a list of Renamings
fromSignRenamings :: Sign -> [Renaming] -> Morphism
fromSignRenamings sg rnms = applyRenamings (createInclMorph sg sg) rnms

applyRenamings :: Morphism -> [Renaming] -> Morphism
applyRenamings m = foldr applyRenaming m

applyRenaming :: Renaming -> Morphism -> Morphism
applyRenaming rnm mor = let
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
                sortMap = Map.insert a b smap
            }
        LabelRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                labelMap = Map.insert a b lmap
            }
        OpRenaming1 from (To to ats) -> let
                a = getName from
                b = getName to
            in mor {
                target = Sign.renameOp a b ats tgt,
                opMap = Map.insert a b omap
            }
        OpRenaming2 from _ _ (To to ats) -> let
        -- TODO: implement real code
                a = getName from
                b = getName to
            in mor {
                target = Sign.renameOp a b ats tgt,
                opMap = Map.insert a b omap
            }
        TermMap _ _ -> mor

-- | extract a Symbol Map from a Morphism
symbolMap :: Morphism -> SymbolMap
symbolMap mor = Map.unions [(sortMap mor), (opMap mor), (labelMap mor)]

-- | create a Morphism from the initial signatures and a list of Renamings
fromSignsRenamings :: Sign -> Sign -> [Renaming] -> Morphism
fromSignsRenamings sg1 sg2 = foldr insertRenaming (createInclMorph sg1 sg2)

-- | insert a Renaming into a Morphism
insertRenaming :: Renaming -> Morphism -> Morphism
insertRenaming rename mor = let
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
    in case rename of
        SortRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                sortMap = Map.insert a b smap
            }
        LabelRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                labelMap = Map.insert a b lmap
            }
        OpRenaming1 from (To to _) -> let
        -- TODO: handle attrs
                a = getName from
                b = getName to
            in mor {
                opMap = Map.insert a b omap
            }
        OpRenaming2 from _ _ (To to _) -> let
        -- TODO: handle attrs
                a = getName from
                b = getName to
            in mor {
                opMap = Map.insert a b omap
            }
        TermMap _ _ -> mor

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
        opMap    = inverseMap (opMap mor),
        labelMap = inverseMap (labelMap mor)
    }

-- | the composition of two Morphisms
-- TODO: Ops don't have labels, so Signs don't have labels. so we can ignore the labelMap. Is that correct?
compose :: Morphism -> Morphism -> Result Morphism
compose f g
    | target f /= source g = fail "target of the first and source of the second morphism are different"
    | otherwise = let
            map'map mp = mapAsFunction (mp g) . mapAsFunction (mp f)
            insert mp x = let y = map'map mp x
                in if x == y then id else Map.insert x y
            compose'map mp items = if Map.null (mp g)
                then mp f
                else Set.fold (insert mp) Map.empty $ items (source f)
        in return (createInclMorph (source f) $ target g) {
                sortMap = compose'map sortMap getSorts,
                opMap = compose'map opMap getOps -- ,
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
        legal'opMap = subset omap getOps
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
        omap = mapOps (opMap mor)
        lmap = mapLabels (labelMap mor)
    in return . lmap . omap . smap

union :: Morphism -> Morphism -> Morphism
union m1 m2 = Morphism {
        source = Sign.union (source m1) $ source m2,
        target = Sign.union (target m1) $ target m2,
        sortMap = Map.union (sortMap m1) $ sortMap m2,
        opMap = Map.union (opMap m1) $ opMap m2,
        labelMap = Map.union (labelMap m1) $ labelMap m2
    }

setTarget :: Sign -> Morphism -> Morphism
setTarget sg morph = morph {target = sg}

renameSorts :: Morphism -> [Symbol] -> [Symbol]
renameSorts m = map f
    where sm = sortMap m
          f = \ x -> if Map.member x sm
                     then fromJust $ Map.lookup x sm
                     else x

extendMorphismSorts :: Morphism -> Symbol -> [Symbol] -> Morphism
extendMorphismSorts mor sym syms = let
       tgt = target mor
       smap = sortMap mor
     in mor {
           target = Sign.renameListSort (createRenaming sym syms) tgt,
           sortMap = extendSortMap sym syms smap
        }

createRenaming :: Symbol -> [Symbol] -> [(Symbol, Symbol)]
createRenaming _ [] = []
createRenaming sym (sym' : syms) = (sym', new_sym) : createRenaming sym syms
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'

extendSortMap :: Symbol -> [Symbol] -> SymbolMap -> SymbolMap
extendSortMap _ [] sm = sm
extendSortMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
             sort_map' = Map.fromList $ extendSortList sym' new_sym $ Map.toList sort_map

extendSortList :: Symbol -> Symbol -> [(Symbol, Symbol)] -> [(Symbol, Symbol)]
extendSortList from to [] = [(from, to)]
extendSortList from to (s@(sym1, sym2) : syms) = if from == sym2
                                               then (sym1, to) : syms
                                               else s : extendSortList from to syms

addQualification :: Morphism -> Symbol -> [Symbol] -> Morphism
addQualification mor sym syms = let
       src = source mor
       smap = sortMap mor
     in mor {
           source = Sign.renameListSort (createRenaming sym syms) src,
           sortMap = qualifyMap sym syms smap
        }

qualifyMap :: Symbol -> [Symbol] -> SymbolMap -> SymbolMap
qualifyMap _ [] sm = sm
qualifyMap sym (sym' : syms) sort_map = extendSortMap sym syms sort_map'
       where new_sym = mkSimpleId $ show sym ++ "$" ++ show sym'
             sort_map' = Map.fromList $ qualifySortList sym' new_sym $ Map.toList sort_map

qualifySortList :: Symbol -> Symbol -> [(Symbol, Symbol)] -> [(Symbol, Symbol)]
qualifySortList from to [] = [(from, to)]
qualifySortList from to (s@(sym1, sym2) : syms) = if from == sym1
                                                  then (to, sym2) : syms
                                                  else s : qualifySortList from to syms

-- TODO: add renaming in operators
applyMorphSign :: Morphism -> Sign -> Sign
applyMorphSign morph = Sign.applySortMap (sortMap morph) . applyOpMap (opMap morph)

applyOpMap :: SymbolMap -> Sign -> Sign
applyOpMap sm sg = sg {Sign.ops = Sign.ops sg}




