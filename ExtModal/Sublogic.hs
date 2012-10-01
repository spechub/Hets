{- |
Module      :  $Header$
Description :  Sublogics for ExtModal logic
Copyright   :  (c) Mihaela Turcu, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  m.turcu@jacobs-university.de
Stability   :  experimental
Portability :  portable

Sublogics for ExtModal Logic
-}

module ExtModal.Sublogic where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Morphism
import CASL.Sign

import Common.AS_Annotation

import Data.Function
import qualified Data.Set as Set

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.MorphismExtension

data Frequency = None | One | Many deriving (Show, Eq, Ord, Enum)

data Sublogic = Sublogic
    { hasModalities :: Frequency
    , hasTermMods :: Bool
    , hasTransClos :: Bool
    , hasNominals :: Bool
    , hasTimeMods :: Frequency
    , hasFixPoints :: Bool
    , hasFrameAxioms :: Bool
    } deriving (Show, Eq, Ord)


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

joinSublogics :: [Sublogic] -> Sublogic
joinSublogics = foldr joinSublogic botSublogic

sublogicRecord :: Record EM_FORMULA Sublogic Sublogic
sublogicRecord = constRecord minSublogicOfEM joinSublogics botSublogic

minSublogicOfForm :: FORMULA EM_FORMULA -> Sublogic
minSublogicOfForm = foldFormula sublogicRecord

minSublogicOfTerm :: TERM EM_FORMULA -> Sublogic
minSublogicOfTerm = foldTerm sublogicRecord

minSublogicOfMod :: MODALITY -> Sublogic
minSublogicOfMod m = case m of
    SimpleMod _ -> botSublogic
    TermMod t -> minSublogicOfTerm t
    ModOp _ m1 m2 -> on joinSublogic minSublogicOfMod m1 m2
    TransClos c -> (minSublogicOfMod c) {hasTransClos = True}
    Guard f -> minSublogicOfForm f

minSublogicOfPrefix :: FormPrefix -> Sublogic
minSublogicOfPrefix fp = case fp of
    BoxOrDiamond _ m _ _ -> minSublogicOfMod m
    Hybrid _ _ -> botSublogic {hasNominals = True}
    FixedPoint _ _ -> botSublogic {hasFixPoints = True}
    _ -> setTimeMods True [()] botSublogic

minSublogicOfEM :: EM_FORMULA -> Sublogic
minSublogicOfEM ef = case ef of
    PrefixForm pf f _ -> joinSublogic (minSublogicOfPrefix pf)
        (minSublogicOfForm f)
    UntilSince _ f1 f2 _ -> setTimeMods True [()]
      $ on joinSublogic minSublogicOfForm f1 f2
    ModForm md -> minSublogicOfModDefn md

minSublogicOfModDefn :: ModDefn -> Sublogic
minSublogicOfModDefn (ModDefn time term il fl _) =
    (setModalities il
    . setTermMods term
    . setTimeMods time il
    . joinSublogics . map (minSublogicOfForm . item)
          $ concatMap (frameForms . item) fl)
    { hasFrameAxioms = not $ null fl }

minSublogicEMSign :: EModalSign -> Sublogic
minSublogicEMSign s = botSublogic
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

minSublogicExtModalSign :: Sign EM_FORMULA EModalSign -> Sublogic
minSublogicExtModalSign = minSublogicEMSign . extendedInfo

-- | mappings do not contribute further nominals or modalities
minSublogicExtModalMorphism :: Morphism EM_FORMULA EModalSign MorphExtension
  -> Sublogic
minSublogicExtModalMorphism m =
  on joinSublogic minSublogicExtModalSign (msource m) $ mtarget m

minSublogicEMBasic :: EM_BASIC_ITEM -> Sublogic
minSublogicEMBasic bi = case bi of
  ModItem md -> minSublogicOfModDefn md
  Nominal_decl l _ -> botSublogic { hasNominals = not $ null l }

minSublogicEMBasicSpec :: EM_BASIC_SPEC -> Sublogic
minSublogicEMBasicSpec (Basic_spec is) =
  joinSublogics $ map (minSLItem . item) is

minSLItem :: BASIC_ITEMS EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA -> Sublogic
minSLItem bi = case bi of
  Ext_BASIC_ITEMS b -> minSublogicEMBasic b
  Axiom_items as _ -> joinSublogics $ map (minSublogicOfForm . item) as
  Local_var_axioms _ as _ -> joinSublogics $ map (minSublogicOfForm . item) as
  Sig_items si -> minSLSigItems si
  Sort_gen is _ -> joinSublogics $ map (minSLSigItems . item) is
  _ -> botSublogic

minSLSigItems :: SIG_ITEMS EM_SIG_ITEM EM_FORMULA -> Sublogic
minSLSigItems si = joinSublogics $ case si of
  Sort_items _ ss _ -> map (minSLSortItem . item) ss
  Op_items os _ -> map (minSLOpItem . item) os
  Pred_items ps _ -> map (minSLPredItem . item) ps
  Datatype_items {} -> []
  Ext_SIG_ITEMS e -> minSLExtSigItem e

minSLExtSigItem :: EM_SIG_ITEM -> [Sublogic]
minSLExtSigItem si = case si of
  Rigid_op_items _ os _ -> map (minSLOpItem . item) os
  Rigid_pred_items _ ps _ -> map (minSLPredItem . item) ps

minSLSortItem :: SORT_ITEM EM_FORMULA -> Sublogic
minSLSortItem si = case si of
  Subsort_defn _ _ _ f _ -> minSublogicOfForm $ item f
  _ -> botSublogic

minSLOpItem :: OP_ITEM EM_FORMULA -> Sublogic
minSLOpItem oi = case oi of
  Op_defn _ _ t _ -> minSublogicOfTerm $ item t
  _ -> botSublogic

minSLPredItem :: PRED_ITEM EM_FORMULA -> Sublogic
minSLPredItem oi = case oi of
  Pred_defn _ _ f _ -> minSublogicOfForm $ item f
  _ -> botSublogic

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

sublogics_all :: [Sublogic]
sublogics_all = let bools = [True, False] in
    [Sublogic
    { hasModalities = h_m
    , hasTermMods = h_term
    , hasTransClos = h_tc
    , hasNominals = h_n
    , hasTimeMods = h_time
    , hasFixPoints = h_fp
    , hasFrameAxioms = hFA
    }
    | h_time <- [None .. Many]
    , h_term <- bools
    , h_m <- [minMod h_term h_time .. Many]
    , h_tc <- bools
    , h_n <- bools
    , h_fp <- bools
    , hFA <- bools
    ]

sublogic_name :: Sublogic -> String
sublogic_name s = (if hasModalities s == Many then "Many" else "One")
    ++ (if hasTermMods s then "Dyn" else "")
    ++ (if hasNominals s then "Hybr" else "")
    ++ (if hasTimeMods s == Many then "Time"
       else if hasTimeMods s == One then "SingleTime" else "")
    ++ (if hasFixPoints s then "Fix" else "")
    ++ (if hasFrameAxioms s then "Frames" else "")
