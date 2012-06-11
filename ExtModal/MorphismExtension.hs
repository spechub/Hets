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
        , nom_map :: Map.Map SIMPLE_ID SIMPLE_ID
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
  { rigidOps = inducedOpMap sm om $ rigidOps ms
  , rigidPreds = inducedPredMap sm pm $ rigidPreds ms
  , modalities = Set.map msm $ modalities ms
  , time_modalities = Set.map msm $ time_modalities ms
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

-- Modal formula mapping via signature morphism
mapEMform :: MapSen EM_FORMULA EModalSign MorphExtension
mapEMform morph frm =
  let rmapf = mapSen mapEMform morph
      em = extended_map morph
  in case frm of
  BoxOrDiamond choice tm leq_geq num f pos ->
    BoxOrDiamond choice (mapEMmod morph tm) leq_geq num (rmapf f) pos
  Hybrid choice nom f pos -> Hybrid choice
    (Map.findWithDefault nom nom $ nom_map em)
    (rmapf f) pos
  UntilSince choice f1 f2 pos -> UntilSince choice (rmapf f1) (rmapf f2) pos
  NextY choice f pos -> NextY choice (rmapf f) pos
  PathQuantification choice f pos -> PathQuantification choice (rmapf f) pos
  StateQuantification t_dir choice f pos ->
    StateQuantification t_dir choice (rmapf f) pos
  FixedPoint choice p_var f pos -> FixedPoint choice p_var (rmapf f) pos
  ModForm (ModDefn ti te is fs pos) -> ModForm $ ModDefn ti te
    (map (fmap $ \ i -> Map.findWithDefault i i
         $ if Set.member i $ sortSet $ msource morph then
         sort_map morph else mod_map em) is)
    (map (fmap rmapf) fs) pos
