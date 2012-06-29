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
import ExtModal.ExtModalSign
import Common.AS_Annotation

data Frequency = None 
               | One 
               | Many
               deriving (Show, Eq, Ord)

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

minSublogic :: Sublogic
minSublogic = Sublogic
    { hasModalities = None
    , hasTermMods = False
    , hasTransClos = False
    , hasNominals = False
    , hasTimeMods = None
    , hasFixPoints = False
    }

joinSublogic :: Sublogic -> Sublogic -> Sublogic
joinSublogic a b = Sublogic
    { hasModalities = hasModalities a `max` hasModalities b
    , hasTermMods = hasTermMods a `max` hasTermMods b
    , hasTransClos = hasTransClos a `max` hasTransClos b
    , hasNominals = hasNominals a `max` hasNominals b
    , hasTimeMods = hasTimeMods a `max` hasTimeMods b
    , hasFixPoints = hasFixPoints a `max` hasFixPoints b
    }

joinSublogics :: [Sublogic] -> Sublogic
joinSublogics = foldr joinSublogic minSublogic

minSublogicOfForm :: FORMULA EM_FORMULA -> Sublogic --ExtModalFORMULA
minSublogicOfForm = foldFormula (constRecord minSublogicOfEM 
                    joinSublogics minSublogic) 

minSublogicOfMod :: MODALITY -> Sublogic
minSublogicOfMod m = case m of 
    SimpleMod _ -> minSublogic
    TermMod t -> foldTerm (constRecord minSublogicOfEM 
                    joinSublogics minSublogic) t
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
    $ joinSublogics (map (minSublogicOfForm . item) fl)

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
    


