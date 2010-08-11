{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

this file defines morhpisms for the reduce logic. A morphism is a mapping of operator symbols
-}


module CSL.Morphism
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
  , morphismUnion
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import CSL.Sign as Sign
import qualified Common.Result as Result
import CSL.AS_BASIC_CSL 
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | The datatype for morphisms in reduce logic as maps of sets
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , operatorMap :: Map.Map Id Id
  } deriving (Eq, Ord, Show)

instance Pretty Morphism where
    pretty = printMorphism

-- | pretty printer for morphisms
printMorphism :: Morphism -> Doc
printMorphism m = pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ operatorMap m)


-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | checks whether a given morphism is legal
isLegalMorphism :: Morphism -> Bool
isLegalMorphism _ = True

-- | calculates the composition of two morhpisms f:X->Y, g:Y->Z
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap    = operatorMap f
      gMap    = operatorMap g
  in return Morphism
  { source = fSource
  , target = gTarget
  , operatorMap = if Map.null gMap then fMap else
      Set.fold ( \ i -> let j = applyMap gMap (applyMap fMap i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ items fSource }

-- | constructs the inclusion map for a given signature
inclusionMap :: Sign.Sign -> Sign.Sign -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , operatorMap = Map.empty }


-- | Application function for propMaps
applyMap :: Map.Map Id Id -> Id -> Id
applyMap operatormap idt = Map.findWithDefault idt idt operatormap


-- | Application funtion for morphisms
applyMorphism :: Morphism -> Id -> Id
applyMorphism mor idt = Map.findWithDefault idt idt $ operatorMap mor


-- | sentence translation along signature morphism
-- here just the renaming of formulae
mapSentence :: Morphism -> CMD -> Result.Result CMD
mapSentence mor = return . mapSentenceH mor

mapSentenceH :: Morphism -> CMD -> CMD
mapSentenceH _ frm = frm

morphismUnion :: Morphism -> Morphism -> Result.Result Morphism
morphismUnion mor1 mor2 =
  let pmap1 = operatorMap mor1
      pmap2 = operatorMap mor2
      p1 = source mor1
      p2 = source mor2
      up1 = Set.difference (items p1) $ Map.keysSet pmap1
      up2 = Set.difference (items p2) $ Map.keysSet pmap2
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
      , operatorMap = pmap } else Result pds Nothing



