{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Temporal/Morphism.hs
Description :  Morphisms in Temporal logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

  Definition of morphisms for temporal logic
  copied from "Propositional.Morphism"

  Ref.

    Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
    What is a Logic?.
    In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
    2005.
-}

module Temporal.Morphism
  ( Morphism (..)               -- datatype for Morphisms
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  , isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  , mapSentence                 -- map of sentences
  , mapSentenceH                -- map of sentences, without Result type
  , applyMap                    -- application function for maps
  , applyMorphism               -- application function for morphism
  ) where

import Data.Data
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

import Temporal.Sign as Sign
import qualified Temporal.AS_BASIC_Temporal as AS_BASIC

import qualified Common.Result as Result
import Common.Result
import Common.Id as Id
import Common.Doc
import Common.DocUtils

import Control.Monad (unless)

{- | The datatype for morphisms in temporal logic as
maps of sets -}
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , propMap :: Map.HashMap Id Id
  } deriving (Eq, Ord, Show, Typeable)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | Determines whether a morphism is valid
isLegalMorphism :: Morphism -> Result ()
isLegalMorphism pmor =
    let psource = items $ source pmor
        ptarget = items $ target pmor
        pdom = Set.fromList $ Map.keys $ propMap pmor
        pcodom = Set.map (applyMorphism pmor) psource
    in unless (Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource) $
        fail "illegal Temporal morphism"

-- | Application funtion for morphisms
applyMorphism :: Morphism -> Id -> Id
applyMorphism mor idt = Map.findWithDefault idt idt $ propMap mor

-- | Application function for propMaps
applyMap :: Map.HashMap Id Id -> Id -> Id
applyMap pmap idt = Map.findWithDefault idt idt pmap

-- | Composition of morphisms in temporal Logic
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap = propMap f
      gMap = propMap g
  in return Morphism
  { source = fSource
  , target = gTarget
  , propMap = if Map.null gMap then fMap else
      Set.fold ( \ i -> let j = applyMap gMap (applyMap fMap i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ items fSource }

-- | Pretty printing for Morphisms
printMorphism :: Morphism -> Doc
printMorphism m = pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.toList $ propMap m) -- TODO:might need sorting!

-- | Inclusion map of a subsig into a supersig
inclusionMap :: Sign.Sign -> Sign.Sign -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , propMap = Map.empty }

{- | sentence translation along signature morphism
here just the renaming of formulae -}
mapSentence :: Morphism -> AS_BASIC.FORMULA -> Result.Result AS_BASIC.FORMULA
mapSentence mor = return . mapSentenceH mor

mapSentenceH :: Morphism -> AS_BASIC.FORMULA -> AS_BASIC.FORMULA
mapSentenceH _ AS_BASIC.Formula = AS_BASIC.Formula
