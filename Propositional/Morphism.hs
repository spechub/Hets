{- |
Module      :  $Header$
Description :  Morphisms in Propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of morphisms for propositional logic
copied to "Temporal.Morphism"
-}
{-
  Ref.

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Morphism
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

import qualified Data.Map as Map
import qualified Data.Set as Set
import Propositional.Sign as Sign
import qualified Common.Result as Result
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | The datatype for morphisms in propositional logic as
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
        pcodom  = Set.map (applyMorphism pmor) $ psource
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
      fTarget = target f
      gSource = source g
      gTarget = target g
      fMap    = propMap f
      gMap    = propMap g
  in if fTarget /= gSource then fail "Morphisms are not composable" else
  return Morphism
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
mapSentence :: Morphism -> AS_BASIC.FORMULA -> Result.Result AS_BASIC.FORMULA
mapSentence mor = return . mapSentenceH mor

-- | gets simple Id
getSimpleId :: Id.Id -> [Id.Token]
getSimpleId (Id toks _ _) = toks

mapSentenceH :: Morphism -> AS_BASIC.FORMULA -> AS_BASIC.FORMULA
mapSentenceH mor frm = case frm of
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
      $ head $ getSimpleId $ applyMorphism mor $ Id.simpleIdToId predH
