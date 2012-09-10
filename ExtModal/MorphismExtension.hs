{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Morphism extension for modal signature morphisms
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

-}

module ExtModal.MorphismExtension where

import qualified Data.Map as Map
import qualified Data.Set as Set

import CASL.Morphism
import CASL.Sign
import CASL.MapSentence

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Utils
import qualified Common.Lib.MapSet as MapSet

import ExtModal.ExtModalSign
import ExtModal.AS_ExtModal
import ExtModal.Print_AS ()

data MorphExtension = MorphExtension
        { mod_map :: Map.Map Id Id
        , nom_map :: Map.Map Id Id
        } deriving (Show, Eq, Ord)

emptyMorphExtension :: MorphExtension
emptyMorphExtension = MorphExtension Map.empty Map.empty

instance Pretty MorphExtension where
        pretty me = pretty (mod_map me) $+$ pretty (nom_map me)

instance MorphismExtension EModalSign MorphExtension where
        ideMorphismExtension _ = emptyMorphExtension
        composeMorphismExtension fme1 fme2 = let
          me1 = extended_map fme1
          me2 = extended_map fme2
          src = msource fme1
          mSrc = extendedInfo src
          in return $ MorphExtension
             (composeMap (MapSet.setToMap $ modalities mSrc) (mod_map me1)
             $ mod_map me2)
             $ composeMap (MapSet.setToMap $ nominals mSrc) (nom_map me1)
             $ nom_map me2
        -- ignore inverses
        isInclusionMorphismExtension me =
                Map.null (mod_map me) && Map.null (nom_map me)

inducedEMsign :: InducedSign EM_FORMULA EModalSign MorphExtension EModalSign
inducedEMsign sm om pm m sig =
  let ms = extendedInfo sig
      mods = mod_map m
      tmods = termMods ms
      msm i = Map.findWithDefault i i
        $ if Set.member i tmods then sm else mods
  in ms
  { flexOps = inducedOpMap sm om $ flexOps ms
  , flexPreds = inducedPredMap sm pm $ flexPreds ms
  , modalities = Set.map msm $ modalities ms
  , timeMods = Set.map msm $ timeMods ms
  , termMods = Set.map (\ i -> Map.findWithDefault i i sm) tmods
  , nominals = Set.map (\ i -> Map.findWithDefault i i $ nom_map m)
    $ nominals ms
  }

mapEMmod :: Morphism EM_FORMULA EModalSign MorphExtension -> MODALITY
  -> MODALITY
mapEMmod morph tm = case tm of
  SimpleMod sm -> case Map.lookup (simpleIdToId sm) $ mod_map
      $ extended_map morph of
    Just ni -> SimpleMod $ idToSimpleId ni
    Nothing -> tm
  ModOp o tm1 tm2 -> ModOp o (mapEMmod morph tm1) $ mapEMmod morph tm2
  TransClos tm1 -> TransClos $ mapEMmod morph tm1
  Guard frm -> Guard $ mapSen mapEMform morph frm
  TermMod trm -> TermMod $ mapTerm mapEMform morph trm

mapEMprefix :: Morphism EM_FORMULA EModalSign MorphExtension -> FormPrefix
  -> FormPrefix
mapEMprefix morph pf = case pf of
  BoxOrDiamond choice tm leq_geq num ->
    BoxOrDiamond choice (mapEMmod morph tm) leq_geq num
  _ -> pf

-- Modal formula mapping via signature morphism
mapEMform :: MapSen EM_FORMULA EModalSign MorphExtension
mapEMform morph frm =
  let rmapf = mapSen mapEMform morph
      em = extended_map morph
  in case frm of
  PrefixForm p f pos -> PrefixForm (mapEMprefix morph p) (rmapf f) pos
  UntilSince choice f1 f2 pos -> UntilSince choice (rmapf f1) (rmapf f2) pos
  ModForm (ModDefn ti te is fs pos) -> ModForm $ ModDefn ti te
    (map (fmap $ \ i -> Map.findWithDefault i i
         $ if Set.member i $ sortSet $ msource morph then
         sort_map morph else mod_map em) is)
    (map (fmap $ mapEMframe morph) fs) pos

mapEMframe :: Morphism EM_FORMULA EModalSign MorphExtension -> FrameForm
  -> FrameForm
mapEMframe morph (FrameForm vs fs r) =
    FrameForm vs (map (fmap $ mapSen mapEMform morph) fs) r
