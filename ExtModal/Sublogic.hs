{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./ExtModal/Sublogic.hs
Description :  Sublogics for ExtModal logic
Copyright   :  (c) DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Sublogics for ExtModal Logic
-}

module ExtModal.Sublogic where

import CASL.AS_Basic_CASL
import CASL.Sublogic

import Common.AS_Annotation

import Data.Data
import Data.Function
import Data.List
import qualified Data.Set as Set

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign

data Frequency = None | One | Many
  deriving (Show, Eq, Ord, Enum, Typeable, Data)

data Sublogic = Sublogic
    { hasModalities :: Frequency
    , hasTermMods :: Bool
    , hasTransClos :: Bool
    , hasNominals :: Bool
    , hasTimeMods :: Frequency
    , hasFixPoints :: Bool
    , hasFrameAxioms :: Bool
    } deriving (Show, Eq, Ord, Typeable, Data)

maxSublogic :: Sublogic
maxSublogic = Sublogic
    { hasModalities = Many
    , hasTermMods = True
    , hasTransClos = True
    , hasNominals = True
    , hasTimeMods = Many
    , hasFixPoints = True
    , hasFrameAxioms = True
    }

botSublogic :: Sublogic
botSublogic = Sublogic
    { hasModalities = None
    , hasTermMods = False
    , hasTransClos = False
    , hasNominals = False
    , hasTimeMods = None
    , hasFixPoints = False
    , hasFrameAxioms = False
    }

-- | the sublogic that can be translated to FOL
foleml :: Sublogic
foleml = maxSublogic
  { hasTimeMods = None
  , hasFixPoints = False
  , hasTransClos = False
  , hasFrameAxioms = False
  }

joinSublogic :: Sublogic -> Sublogic -> Sublogic
joinSublogic a b =
  let onMax f = on max f a b
      termM = onMax hasTermMods
      timeM = onMax hasTimeMods
  in Sublogic
    { hasModalities = minMod termM timeM
        `max` onMax hasModalities
    , hasTermMods = termM
    , hasTransClos = onMax hasTransClos
    , hasNominals = onMax hasNominals
    , hasTimeMods = timeM
    , hasFixPoints = onMax hasFixPoints
    , hasFrameAxioms = onMax hasFrameAxioms
    }

instance Lattice Sublogic where
  cjoin = joinSublogic
  ctop = maxSublogic
  bot = botSublogic

joinSublogics :: [Sublogic] -> Sublogic
joinSublogics = foldr joinSublogic botSublogic

type ExtModalSL = CASL_SL Sublogic

minSublogicOfForm :: FORMULA EM_FORMULA -> ExtModalSL
minSublogicOfForm = sl_sentence minSublogicOfEM

minSublogicOfTerm :: TERM EM_FORMULA -> ExtModalSL
minSublogicOfTerm = sl_term minSublogicOfEM

minSublogicOfMod :: MODALITY -> ExtModalSL
minSublogicOfMod m = case m of
    SimpleMod _ -> bottom
    TermMod t -> minSublogicOfTerm t
    ModOp _ m1 m2 -> on sublogics_max minSublogicOfMod m1 m2
    TransClos c -> updExtFeature (\ s -> s {hasTransClos = True})
      (minSublogicOfMod c)
    Guard f -> minSublogicOfForm f

minSublogicOfPrefix :: FormPrefix -> ExtModalSL
minSublogicOfPrefix fp = case fp of
    BoxOrDiamond _ m _ _ -> minSublogicOfMod m
    Hybrid _ _ -> mkBot botSublogic {hasNominals = True}
    FixedPoint _ _ -> mkBot botSublogic {hasFixPoints = True}
    _ -> updExtFeature (setTimeMods True [()]) bottom

minSublogicOfEM :: EM_FORMULA -> ExtModalSL
minSublogicOfEM ef = case ef of
    PrefixForm pf f _ -> sublogics_max (minSublogicOfPrefix pf)
        (minSublogicOfForm f)
    UntilSince _ f1 f2 _ -> updExtFeature (setTimeMods True [()])
      $ on sublogics_max minSublogicOfForm f1 f2
    ModForm md -> minSublogicOfModDefn md

minSublogicOfModDefn :: ModDefn -> ExtModalSL
minSublogicOfModDefn (ModDefn time term il fl _) =
    updExtFeature (\ s -> s {hasFrameAxioms = not $ null fl})
    . updExtFeature (setModalities il)
    . updExtFeature (setTermMods term)
    . updExtFeature (setTimeMods time il)
    . comp_list . map (minSublogicOfForm . item)
          $ concatMap (frameForms . item) fl

minSublogicEMSign :: EModalSign -> ExtModalSL
minSublogicEMSign s = mkBot botSublogic
  { hasTermMods = not . Set.null $ termMods s
  , hasTimeMods = case Set.size $ timeMods s of
      0 -> None
      1 -> One
      _ -> Many
  , hasNominals = not . Set.null $ nominals s
  , hasModalities = case Set.size $ modalities s of
      0 -> None
      1 -> One
      _ -> Many
  }

minSublogicEMBasic :: EM_BASIC_ITEM -> ExtModalSL
minSublogicEMBasic bi = case bi of
  ModItem md -> minSublogicOfModDefn md
  Nominal_decl l _ -> mkBot botSublogic { hasNominals = not $ null l }

minSLExtSigItem :: EM_SIG_ITEM -> [ExtModalSL]
minSLExtSigItem si = case si of
  Rigid_op_items _ os _ -> map (sl_op_item minSublogicOfEM . item) os
  Rigid_pred_items _ ps _ -> map (sl_pred_item minSublogicOfEM . item) ps

setModalities :: [a] -> Sublogic -> Sublogic
setModalities il s = case il of
    [_] -> s {hasModalities = max One (hasModalities s)}
    _ -> s {hasModalities = Many}

setTermMods :: Bool -> Sublogic -> Sublogic
setTermMods b s = if b then s {hasTermMods = True} else s

setTimeMods :: Bool -> [a] -> Sublogic -> Sublogic
setTimeMods b il s = if b then case il of
    [_] -> s {hasTimeMods = max One (hasTimeMods s)}
    _ -> s {hasTimeMods = Many}
    else s

minMod :: Bool -> Frequency -> Frequency
minMod h_term h_time = if h_term && h_time == None then One
  else h_time

sublogicsDim :: [[Sublogic]]
sublogicsDim = let
  t = True
  b = bot
  f = [One, Many]
  in [ [ b { hasModalities = h } | h <- f]
     , [ b { hasTermMods = t }]
     , [ b { hasTransClos = t }]
     , [ b { hasNominals = t }]
     , [ b { hasModalities = h } | h <- f]
     , [ b { hasFixPoints = t }]
     , [ b { hasFrameAxioms = t }] ]

sublogName :: Sublogic -> String
sublogName s = (if hasModalities s == Many then "Many" else "One")
    ++ (if hasTermMods s then "Dyn" else "")
    ++ (if hasNominals s then "Hybr" else "")
    ++ (if hasTimeMods s == Many then "Time"
       else if hasTimeMods s == One then "SingleTime" else "")
    ++ (if hasFixPoints s then "Fix" else "")
    ++ (if hasFrameAxioms s then "Frames" else "")
    ++ if hasTransClos s then "*" else ""

parseSublog :: String -> (Sublogic, String)
parseSublog s0 = let
  (m, s1) = case stripPrefix "Many" s0 of
    Nothing -> case stripPrefix "One" s0 of
      Nothing -> (None, s0)
      Just r -> (One, r)
    Just r -> (Many, r)
  (tm, s2) = parseBool "Dyn" s1
  (n, s3) = parseBool "Hybr" s2
  (ti, s4) = case stripPrefix "Time" s3 of
    Just r -> (Many, r)
    Nothing -> case stripPrefix "SingleTime" s3 of
      Nothing -> (None, s3)
      Just r -> (One, r)
  (fi, s5) = parseBool "Fix" s4
  (fr, s6) = parseBool "Frames" s5
  (tr, s7) = parseBool "*" s6
  in (Sublogic
    { hasModalities = max m $ minMod tm ti
    , hasTermMods = tm
    , hasTransClos = tr
    , hasNominals = n
    , hasTimeMods = ti
    , hasFixPoints = fi
    , hasFrameAxioms = fr
    }, s7)
