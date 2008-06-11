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
    fromRenamingSet,
    identity,
    compose,
    isLegal
) where

import Maude.Meta

import Maude.Sign hiding (empty, isLegal)
import qualified Maude.Sign as Sign (empty, isLegal)

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Result as Result

type SortMap = Map.Map Qid Qid
type OpMap = Map.Map Qid Qid
type LabelMap = Map.Map Qid Qid

data Morphism = Morphism {
        source :: Sign,
        target :: Sign,
        sortMap :: SortMap,
        opMap :: OpMap,
        labelMap :: LabelMap
    } deriving (Show, Eq)

-- | extract a Morphism from a RenamingSet
fromRenamingSet :: RenamingSet -> Morphism
fromRenamingSet = Set.fold insertRenaming empty

-- | insert a Renaming into a Morphism
insertRenaming :: Renaming -> Morphism -> Morphism
insertRenaming rename mor = let
        src = source mor
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
        op nam as cod dom = Op { op'name = nam, op'range = cod, op'domain = dom, op'attrs = as }
    in case rename of
        Sort'To {from = a, to = b} -> mor {
                source = insertSort a src,
                target = insertSort b tgt,
                sortMap = Map.insert a b smap
            }
        Op'To {from = a, to = b} -> mor {
                source = insertOpName a src,
                target = insertOpName b tgt,
                opMap = Map.insert a b omap
            }
        Op'Type'To {from = a, range = cod, domain = dom, to = b, attrs = as} -> mor {
                source = insertOp (op a as cod dom) src,
                target = insertOp (op b as cod dom) tgt,
                opMap = Map.insert a b omap
            }
        Label'To {from = a, to = b} -> mor {
                labelMap = Map.insert a b lmap
            }

-- | the empty Morphism
empty :: Morphism
empty = identity Sign.empty

-- | the identity Morphism
identity :: Sign -> Morphism
identity sign = Morphism {
        source = sign,
        target = sign,
        sortMap = Map.empty,
        opMap = Map.empty,
        labelMap = Map.empty
    }

-- | the composition of two Morphisms
compose :: Morphism -> Morphism -> Result.Result Morphism
compose f g
    | (target f) /= (source g) = fail "target of the first and source of the second morphism are different"
    | otherwise = let
            apply mp nam = Map.findWithDefault nam nam mp
            map'map mp = apply (mp g) . apply (mp f)
            insert mp x = let y = map'map mp x
                in if x == y then id else Map.insert x y
            compose'map mp items = if Map.null (mp g)
                then mp f
                else Set.fold (insert mp) Map.empty $ items (source f)
        in return Morphism {
                source = (source f),
                target = (target g),
                sortMap = compose'map sortMap sorts,
                opMap = compose'map opMap opNames,
                labelMap = compose'map labelMap labels
            }

-- | check that a Morphism is legal
isLegal :: Morphism -> Bool
isLegal mor = let
        src = source mor
        tgt = target mor
        smap = sortMap mor
        omap = opMap mor
        lmap = labelMap mor
        apply mp nam = Map.findWithDefault nam nam mp
        subset mp items = Set.isSubsetOf (Set.map (apply mp) $ items src) (items tgt)
        legal'source = Sign.isLegal src
        legal'sortMap = subset smap sorts
        legal'opMap = subset omap opNames
        legal'labelMap = subset lmap labels
        legal'target = Sign.isLegal tgt
    in all id [legal'source, legal'sortMap, legal'opMap, legal'labelMap, legal'target]
