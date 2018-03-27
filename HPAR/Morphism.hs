{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPAR/Morphism.hs
Description :  Morphisms in HPAR
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.cm
Stability   :  experimental
Portability :  portable

  Definition of morphisms for HPAR
  
-}

module HPAR.Morphism
  ( HMorphism (..)               -- datatype for Morphisms
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  --, isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  --, mapSentence                 -- map of sentences
  --, mapSentenceH                -- map of sentences, without Result type
  --, applyMap                    -- application function for maps
  --, applyMorphismProp
  --, applyMorphismNom
  --, morphismUnion
  ) where

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified RigidCASL.Sign as PARSign
import HPAR.Sign as Sign
import qualified RigidCASL.AS_Rigid as Rigid_BASIC
import qualified CASL.Morphism as CASL_Mor

import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils
import qualified Common.Result as Result

import Control.Monad (unless)

{- | The datatype for morphisms in propositional logic as
maps of sets -}
data HMorphism = HMorphism
  { source :: HSign
  , target :: HSign
  , baseMor :: CASL_Mor.Morphism () () ()
  , nomMap :: Map.Map Id Id
  , modMap :: Map.Map Id Id
  } deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty HMorphism where
    pretty = printMorphism


-- | Constructs an id-morphism
idMor :: HSign -> HMorphism
idMor a = inclusionMap a a

{-
-- | Determines whether a morphism is valid
isLegalMorphism :: HMorphism -> Result ()
isLegalMorphism pmor =
    let psource = PSign.items $ propSig $ source pmor
        nsource = noms $ source pmor
        ptarget = PSign.items $ propSig $ target pmor
        ntarget = noms $ target pmor
        pdom = Map.keysSet $ propMap pmor
        pcodom = Set.map (applyMorphismProp pmor) psource
        ndom = Map.keysSet $ nomMap pmor
        ncodom = Set.map (applyMorphismNom pmor) nsource
    in unless (Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource
             &&Set.isSubsetOf ncodom ntarget && Set.isSubsetOf ndom nsource) $
        fail "illegal hybrid propositional morphism"
-}

{-

-- | Application funtion for props
applyMorphismProp :: HMorphism -> Id -> Id
applyMorphismProp mor = PMorphism.applyMap $ propMap mor

-- | Application funtion for noms
applyMorphismNom :: HMorphism -> Id -> Id
applyMorphismNom mor = PMorphism.applyMap $ nomMap mor

-- | Application funtion for noms
applyMorphismNom :: HMorphism -> Id -> Id
applyMorphismNom mor = PMorphism.applyMap $ nomMap mor

-}

-- | Composition of morphisms in propositional Logic
composeMor :: HMorphism -> HMorphism -> Result HMorphism
composeMor f g = error "composeMor nyi"{-
  let fSource = source f
      gTarget = target g
      fpMap = propMap f
      gpMap = propMap g
      fnMap = nomMap f
      gnMap = nomMap g
  in return HMorphism -- TODO: this always works????
  { source = fSource
  , target = gTarget
  , propMap = if Map.null gpMap then fpMap else
      Set.fold ( \ i -> let j = applyMorphismProp g (applyMorphismProp f i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ PSign.items $ propSig fSource
  , nomMap = if Map.null gnMap then fnMap else
      Set.fold ( \ i -> let j = applyMorphismNom g (applyMorphismNom f i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ noms fSource
  }
-}

-- | Pretty printing for Morphisms
printMorphism :: HMorphism -> Doc
printMorphism m = error "printMorphism nyi"
 {-pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ propMap m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ nomMap m)
-}

-- | Inclusion map of a subsig into a supersig
inclusionMap :: HSign -> HSign -> HMorphism
inclusionMap s1 s2 = HMorphism
  { source  = s1
  , target  = s2
  , baseMor = undefined -- should be inclusion between the base sigs
  , nomMap = Map.empty
  , modMap  = Map.empty }


{- | sentence translation along signature morphism
here just the renaming of formulae  ----------------------- TODO
mapSentence :: Morphism -> AS_BASIC.FORMULA -> Result.Result AS_BASIC.FORMULA
mapSentence mor = return . mapSentenceH mor

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
      $ id2SimpleId $ applyMorphism mor $ Id.simpleIdToId predH
-}

{- TODO
morphismUnion :: HMorphism -> HMorphism -> Result.Result HMorphism
morphismUnion mor1 mor2 =
  let pmap1 = propMap mor1
      pmap2 = propMap mor2
      nmap1 = nomMap mor1
      nmap2 = nomMap mor2
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
-}



