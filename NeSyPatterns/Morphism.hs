{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./NeSyPatterns/Morphism.hs
Description :  Morphisms in NeSyPatterns logic
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till.mossakowski@ovgu.de
Stability   :  experimental
Portability :  portable

  Definition of morphisms for neural-symbolic patterns
-}

module NeSyPatterns.Morphism
  ( Morphism (..)               -- datatype for Morphisms
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  , isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  , applyMap                    -- application function for maps
  , applyMorphism               -- application function for morphism
  , morphismUnion
  ) where

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

import NeSyPatterns.Sign as Sign
import NeSyPatterns.AS

import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils
import qualified Common.Result as Result

import Control.Monad (unless)

{- | Morphisms are graph homomorphisms, here: node maps -}
data Morphism = Morphism
  { source :: Sign.Sign
  , target :: Sign.Sign
  , nodeMap :: Map.Map Node Node
  } deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | Determines whether a morphism is valid
isLegalMorphism :: Morphism -> Result ()
isLegalMorphism pmor =
    let psource = nodes $ source pmor
        ptarget = nodes $ target pmor
        pdom = Map.keysSet $ nodeMap pmor
        pcodom = Set.map (applyMorphism pmor) psource
    in unless (Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource) $
        fail "illegal NeSyPatterns morphism"

-- | Application funtion for morphisms
applyMorphism :: Morphism -> Node -> Node
applyMorphism mor idt = Map.findWithDefault idt idt $ nodeMap mor

-- | Application function for nodeMaps
applyMap :: Map.Map Node Node -> Node -> Node
applyMap pmap idt = Map.findWithDefault idt idt pmap

-- | Composition of morphisms in propositional Logic
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap = nodeMap f
      gMap = nodeMap g
  in return Morphism
  { source = fSource
  , target = gTarget
  , nodeMap = if Map.null gMap then fMap else
      Set.fold ( \ i -> let j = applyMap gMap (applyMap fMap i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ nodes fSource }

-- | Pretty printing for Morphisms
printMorphism :: Morphism -> Doc
printMorphism m = pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ nodeMap m)

-- | Inclusion map of a subsig into a supersig
inclusionMap :: Sign.Sign -> Sign.Sign -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , nodeMap = Map.empty }


morphismUnion :: Morphism -> Morphism -> Result.Result Morphism
morphismUnion mor1 mor2 =
  let pmap1 = nodeMap mor1
      pmap2 = nodeMap mor2
      p1 = source mor1
      p2 = source mor2
      up1 = Set.difference (nodes p1) $ Map.keysSet pmap1
      up2 = Set.difference (nodes p2) $ Map.keysSet pmap2
      (pds, pmap) = foldr ( \ (i, j) (ds, m) -> case Map.lookup i m of
          Nothing -> (ds, Map.insert i j m)
          Just k -> if j == k then (ds, m) else
              (Diag Error
               ("incompatible mapping of prop " ++ showId i " to "
                ++ showId j " and " ++ showId k "")
               nullRange : ds, m)) ([], pmap1)
          (Map.toList pmap2 ++ map (\ a -> (a, a))
                      (Set.toList $ Set.union up1 up2))
   in if null pds then return Morphism
      { source = unite p1 p2
      , target = unite (target mor1) $ target mor2
      , nodeMap = pmap } else Result pds Nothing
