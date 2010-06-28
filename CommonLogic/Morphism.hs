{- |
Module      :  $Header$
Description :  Morphism of Common Logic
Copyright   :  (c) Uni Bremen DFKI 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

Morphism of Common Logic

-}

module CommonLogic.Morphism
  ( Morphism (..) 
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
import qualified Common.Result as Result
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

import CommonLogic.AS_CommonLogic as AS_BASIC
import CommonLogic.Sign as Sign
-- import Common.DefaultMorphism

-- type Morphism = DefaultMorphism Sign

--   maps of sets
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , propMap :: Map.Map Id Id
  } deriving (Eq, Ord, Show)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | Determines whether a morphism is valid
isLegalMorphism :: Morphism -> Bool
isLegalMorphism pmor =
    let psource = items $ source pmor
        ptarget = items $ target pmor
        pdom    = Map.keysSet $ propMap pmor
        pcodom  = Set.map (applyMorphism pmor) psource
    in Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource

-- | Application funtion for morphisms
applyMorphism :: Morphism -> Id -> Id
applyMorphism mor idt = Map.findWithDefault idt idt $ propMap mor

-- | Application function for propMaps
applyMap :: Map.Map Id Id -> Id -> Id
applyMap pmap idt = Map.findWithDefault idt idt pmap

-- | Composition of morphisms in propositional Logic
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap    = propMap f
      gMap    = propMap g
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
  <> pretty y <> rparen) $ Map.assocs $ propMap m)

-- | Inclusion map of a subsig into a supersig
inclusionMap :: Sign.Sign -> Sign.Sign -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , propMap = Map.empty }

-- | sentence translation along signature morphism
-- here just the renaming of formulae
mapSentence :: Morphism -> AS_BASIC.SENTENCE -> Result.Result AS_BASIC.SENTENCE
mapSentence mor = return . mapSentenceH mor

mapSentenceH :: Morphism -> AS_BASIC.SENTENCE -> AS_BASIC.SENTENCE
mapSentenceH mor frm = case frm of
  AS_BASIC.Quant_sent sen rn -> case sen of
    AS_BASIC.Universal ns sen -> sen -- fix

{-
  AS_BASIC.Quant_sent form rn -> case form of
  AS_BASIC.Negation form rn -> AS_BASIC.Negation (mapSentenceH mor form) rn
  AS_BASIC.Conjunction form rn ->
      AS_BASIC.Conjunction (map (mapSentenceH mor) form) rn
  AS_BASIC.Disjunction form rn ->
      AS_BASIC.Disjunction (map (mapSentenceH mor) form) rn
  AS_BASIC.Implication form1 form2 rn -> AS_BASIC.Implication
      (mapSentenceH mor form1) (mapSentenceH mor form2) rn
  AS_BASIC.Equivalence form1 form2 rn -> AS_BASIC.Equivalence
      (mapSentenceH mor form1) (mapSentenceH mor form2) rn
  AS_BASIC.True_atom rn -> AS_BASIC.True_atom rn
  AS_BASIC.False_atom rn -> AS_BASIC.False_atom rn
  AS_BASIC.Predication predH -> AS_BASIC.Predication
      $ id2SimpleId $ applyMorphism mor $ Id.simpleIdToId predH
-}

morphismUnion :: Morphism -> Morphism -> Result.Result Morphism
morphismUnion mor1 mor2 =
  let pmap1 = propMap mor1
      pmap2 = propMap mor2
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
      , propMap = pmap } else Result pds Nothing
