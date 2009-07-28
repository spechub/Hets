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
    fromRenamings,
    fromSignRenamings,
    symbolMap,
    empty,
    identity,
    createInclMorph,
    inverse,
    compose,
    isLegal,
    isInclusion,
    mapSentence,
    setTarget
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
  pretty m = Doc.text $ "\n\nMorphism:\n\n" ++ printMorphism (sortMap m) (opMap m) (labelMap m)
                        ++ "\n\nTarget:\n\n" ++ printSign (Sign.sorts sign) (Sign.subsorts sign) (Sign.ops sign)
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

-- | extract a Morphism from a list of Renamings
fromRenamings :: [Renaming] -> Morphism
fromRenamings = foldr insertRenaming empty

-- | extract a Symbol Map from a Morphism
symbolMap :: Morphism -> SymbolMap
symbolMap mor = Map.unions [(sortMap mor), (opMap mor), (labelMap mor)]

-- | insert a Renaming into a Morphism
insertRenaming :: Renaming -> Morphism -> Morphism
insertRenaming rename mor = let
        src = source mor
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
    in case rename of
        SortRenaming from to -> let
                a = getName from
                b = getName to
            in mor {
                source = Sign.insertSort from src,
                target = Sign.insertSort to tgt,
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
                source = Sign.insertOpName from src,
                target = Sign.insertOpName to tgt,
                opMap = Map.insert a b omap
            }
        OpRenaming2 from _ _ (To to _) -> let
        -- TODO: handle attrs
                a = getName from
                b = getName to
            in mor {
                source = Sign.insertOpName from src,
                target = Sign.insertOpName to tgt,
                opMap = Map.insert a b omap
            }

-- | the empty Morphism
empty :: Morphism
empty = identity Sign.empty

-- | the identity Morphism
identity :: Sign -> Morphism
identity sign = createInclMorph sign sign

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

setTarget :: Sign -> Morphism -> Morphism
setTarget sg morph = morph {target = sg}
