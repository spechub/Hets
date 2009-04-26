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
    symbolMap,
    identity,
    compose,
    inverse,
    isInclusion,
    isLegal,
    mapSentence,
) where

import Maude.Meta
import Maude.Symbol
import Maude.Sentence

import Maude.Sign (Sign)
import qualified Maude.Sign as Sign

import Data.Set (Set)
import Data.Map (Map)
import Data.Typeable (Typeable)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Result (Result)
import qualified Common.Result as Result

-- for ShATermConvertible
import Common.ATerm.Conversion (ShATermConvertible(..))
-- for Pretty
import Common.DocUtils (Pretty(..))
import qualified Common.Doc as Doc


type SortMap = Map Symbol Symbol
type OpMap = Map Symbol Symbol
type LabelMap = Map Symbol Symbol

data Morphism = Morphism {
        source :: Sign,
        target :: Sign,
        sortMap :: SortMap,
        opMap :: OpMap,
        labelMap :: LabelMap
    } deriving (Show, Eq, Ord, Typeable)

-- TODO: Add real pretty-printing for Maude Morphisms.
instance Pretty Morphism where
    pretty _ = Doc.empty

-- TODO: Replace dummy implementation for ShATermConvertible Morphism.
instance ShATermConvertible Morphism where
    toShATermAux table _ = return (table, 0)
    fromShATermAux _ table = (table, empty)

-- | extract a Morphism from a RenamingSet
fromRenamingSet :: RenamingSet -> Morphism
fromRenamingSet = Set.fold insertRenaming empty

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
        op nam as cod dom = Op { op'name = nam, op'range = cod, op'domain = dom, op'attrs = as }
    in case rename of
        Sort'To {from = a, to = b} -> mor {
                source = Sign.insertSort a src,
                target = Sign.insertSort b tgt,
                sortMap = Map.insert a b smap
            }
        Op'To {from = a, to = b} -> mor {
                source = Sign.insertOpName a src,
                target = Sign.insertOpName b tgt,
                opMap = Map.insert a b omap
            }
        Op'Type'To {from = a, range = cod, domain = dom, to = b, attrs = as} -> mor {
                source = Sign.insertOp (op a as cod dom) src,
                target = Sign.insertOp (op b as cod dom) tgt,
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
compose :: Morphism -> Morphism -> Result Morphism
compose f g
    | target f /= source g = fail "target of the first and source of the second morphism are different"
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
                sortMap = compose'map sortMap getSorts,
                opMap = compose'map opMap getOps,
                labelMap = compose'map labelMap getLabels
            }

-- | the inverse of a Morphism
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

-- | check that a Morphism is an Inclusion
isInclusion :: Morphism -> Bool
-- TODO: Implement Morphism.isInclusion.
isInclusion mor = False

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
        legal'sortMap = subset smap getSorts
        legal'opMap = subset omap getOps
        legal'labelMap = subset lmap getLabels
        legal'target = Sign.isLegal tgt
    in all id [legal'source, legal'sortMap, legal'opMap, legal'labelMap, legal'target]

-- | translate a Sentence along a Morphism
mapSentence :: Morphism -> Sentence -> Result.Result Sentence
mapSentence mor = let
        smap = mapSorts (sortMap mor)
        omap = mapOps (opMap mor)
        lmap = mapLabels (labelMap mor)
    in return . lmap . omap . smap
