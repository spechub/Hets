{- |
Module      :  $Header$
Description :  Morphisms in Propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for propositional logic
-}
{-
  Ref.

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Temporal.Morphism
    (
     Morphism (..)               -- datatype for Morphisms
    ,pretty                      -- pretty printing
    ,idMor                       -- identity morphism
    ,isLegalMorphism             -- check if morhpism is ok
    ,composeMor                  -- composition
    ,inclusionMap                -- inclusion map
    ,mapSentence                 -- map of sentences
    ,mapSentenceH                -- map of sentences, without Result type
    ,applyMap                    -- application function for maps
    ,applyMorphism               -- application function for morphism
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Temporal.Sign as Sign
import qualified Common.Result as Result
import qualified Temporal.AS_BASIC_Temporal as AS_BASIC
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | The datatype for morphisms in propositional logic as
-- | maps of sets

data Morphism = Morphism
    {
       source :: Sign
     , target :: Sign
     , propMap :: Map.Map Id Id
    } deriving (Eq, Ord, Show)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism as the diagonal

idMor :: Sign -> Morphism
idMor a = Morphism
          { source = a
          , target = a
          , propMap = makeIdMor $ items a
          }
    where
      makeIdMor :: (Ord b) => Set.Set b -> Map.Map b b
      makeIdMor b = Set.fold (\x -> Map.insert x x) Map.empty b

-- | Determines whether a morphism is valid
isLegalMorphism :: Morphism -> Bool
isLegalMorphism pmor =
    let
        psource = items $ source pmor
        ptarget = items $ target pmor
        pdom    = Map.keysSet $ propMap pmor
        pcodom  = Set.map (applyMorphism pmor) $ psource
    in
      Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource

-- | Application funtion for morphisms
applyMorphism :: Morphism -> Id -> Id
applyMorphism mor idt = Map.findWithDefault idt idt $ propMap mor

-- | Application function for propMaps
applyMap :: Map.Map Id Id -> Id -> Id
applyMap pmap idt = Map.findWithDefault idt idt pmap

-- | Composition of morphisms in propositional Logic
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g
    | fTarget /= gSource = fail "Morphisms are not composable"
    | otherwise = return Morphism
                  {
                    source = fSource
                  , target = gTarget
                  , propMap = if Map.null gMap then fMap else
                                  Set.fold ( \ i ->
                                                 let j = applyMap gMap (applyMap fMap i) in
                                                 if i == j then id else Map.insert i j)
                                  Map.empty $ items fSource
                  }
    where
      fSource = source f
      fTarget = target f
      gSource = source g
      gTarget = target g
      fMap    = propMap f
      gMap    = propMap g

-- | Pretty printing for Morphisms
printMorphism :: Morphism -> Doc
printMorphism m = pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ propMap m)

-- | Inclusion map of a subsig into a supersig
inclusionMap :: Sign.Sign -> Sign.Sign -> Result Morphism
inclusionMap s1 s2
    |isSub = Result.Result
             {
               diags = [Diag
                        {
                          Result.diagKind   = Result.Debug
                        , Result.diagString = "All fine"
                        , diagPos           = Id.nullRange
                        }]
             , maybeResult = Just $ Morphism
               {
                 source = s1
               , target = s2
               , propMap = Set.fold (\x -> Map.insert x x)
                           Map.empty (Sign.items s1)
               }
             }
    | otherwise = Result.Result
             {
               diags = [Diag
                        {
                          Result.diagKind   = Result.Error
                        , Result.diagString = errorStr
                        , diagPos           = Id.nullRange
                        }]
             , maybeResult = Nothing
             }

    where
      isSub = Sign.isSubSigOf s1 s2
      errorStr = (show $ pretty s1) ++ " is not subset of " ++ (show $ pretty s2)

-- | sentence translation along signature morphism
-- here just the renaming of formulae
mapSentence :: Morphism -> AS_BASIC.FORMULA -> Result.Result AS_BASIC.FORMULA
mapSentence mor form = Result.Result
                       {
                         diags = [Diag
                                  {
                                    Result.diagKind   = Result.Debug
                                  , Result.diagString = "All fine mapSentence"
                                  , diagPos           = Id.nullRange
                                  }]
                       , maybeResult = Just $ mapSentenceH mor form
                       }

mapSentenceH :: Morphism -> AS_BASIC.FORMULA -> AS_BASIC.FORMULA
mapSentenceH _ AS_BASIC.Formula = AS_BASIC.Formula

