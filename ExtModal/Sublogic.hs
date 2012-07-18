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

import CASL.Fold
import CASL.AS_Basic_CASL
import ExtModal.AS_ExtModal
import Common.AS_Annotation
-- import ExtModal.ExtModalSign


data Frequency = None
               | One
               | Many
               deriving (Show, Eq, Ord, Enum)

data Sublogic = Sublogic
    { hasModalities :: Frequency
    , hasTermMods :: Bool
    , hasTransClos :: Bool
    , hasNominals :: Bool
    , hasTimeMods :: Frequency
    , hasFixPoints :: Bool
    }
    deriving (Show, Eq, Ord)


maxSublogic :: Sublogic
maxSublogic = Sublogic
    { hasModalities = Many
    , hasTermMods = True
    , hasTransClos = True
    , hasNominals = True
    , hasTimeMods = Many
    , hasFixPoints = True
    }

botSublogic :: Sublogic
botSublogic = Sublogic
    { hasModalities = None
    , hasTermMods = False
    , hasTransClos = False
    , hasNominals = False
    , hasTimeMods = None
    , hasFixPoints = False
    }

joinSublogic :: Sublogic -> Sublogic -> Sublogic
joinSublogic a b =
  let termM = hasTermMods a `max` hasTermMods b
      timeM = hasTimeMods a `max` hasTimeMods b
  in Sublogic
    { hasModalities = minMod termM timeM
        `max` hasModalities a `max` hasModalities b
    , hasTermMods = termM
    , hasTransClos = hasTransClos a `max` hasTransClos b
    , hasNominals = hasNominals a `max` hasNominals b
    , hasTimeMods = timeM
    , hasFixPoints = hasFixPoints a `max` hasFixPoints b
    }

joinSublogics :: [Sublogic] -> Sublogic
joinSublogics = foldr joinSublogic botSublogic

minSublogicOfForm :: FORMULA EM_FORMULA -> Sublogic
minSublogicOfForm = foldFormula (constRecord minSublogicOfEM
                    joinSublogics botSublogic)

minSublogicOfMod :: MODALITY -> Sublogic
minSublogicOfMod m = case m of
    SimpleMod _ -> botSublogic
    TermMod t -> foldTerm (constRecord minSublogicOfEM
        joinSublogics botSublogic) t
    ModOp _ m1 m2 -> joinSublogic (minSublogicOfMod m1)
        (minSublogicOfMod m2)
    TransClos c -> (minSublogicOfMod c) {hasTransClos = True}
    Guard f -> minSublogicOfForm f


minSublogicOfEM :: EM_FORMULA -> Sublogic
minSublogicOfEM ef = case ef of
    BoxOrDiamond _ m _ _ f _ -> joinSublogic (minSublogicOfMod m)
        (minSublogicOfForm f)
    Hybrid _ _ f _ -> (minSublogicOfForm f) {hasNominals = True}
    UntilSince _ f1 f2 _ -> joinSublogic (minSublogicOfForm f1)
        (minSublogicOfForm f2)
    PathQuantification _ f _ -> minSublogicOfForm f
    NextY _ f _ -> minSublogicOfForm f
    StateQuantification _ _ f _ -> minSublogicOfForm f
    FixedPoint _ _ f _ -> (minSublogicOfForm f) {hasFixPoints = True}
    ModForm md -> minSublogicOfModDefn md


minSublogicOfModDefn :: ModDefn -> Sublogic
minSublogicOfModDefn (ModDefn time term il fl _) =
    setModalities il
    $ setTermMods term
    $ setTimeMods time il
    $ joinSublogics (map (minSublogicOfForm . item)
                     $ concatMap (frameForms . item) fl)


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
minMod h_term h_time = if h_term then
  if h_time == None then One else Many
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
    }
    | h_time <- [None .. Many]
    , h_term <- bools
    , h_m <- [minMod h_term h_time .. Many]
    , h_tc <- bools
    , h_n <- bools
    , h_fp <- bools
    ]

sublogic_name :: Sublogic -> String
sublogic_name s = (if hasModalities s == Many then "Many" else "One")
    ++ (if hasTermMods s then "Dyn" else "")
    ++ (if hasNominals s then "Hybr" else "")
    ++ (if hasTimeMods s == Many then "MTime"
       else if hasTimeMods s == One then "OTime" else "")
    ++ (if hasFixPoints s then "Fix" else "")
