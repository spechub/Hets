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

data Frequency = None | One | Many
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

joinSublogic :: Sublogic -> Sublogic -> Sublogic
joinSublogic a b = Sublogic
  { hasModalities = hasModalities a `max` hasModalities b
  , hasTermMods = hasTermMods a `max` hasTermMods b
  , hasTransClos = hasTransClos a `max` hasTransClos b
  , hasNominals = hasNominals a `max` hasNominals b
  , hasTimeMods = hasTimeMods a `max` hasTimeMods b
  , hasFixPoints = hasFixPoints a `max` hasFixPoints b
        }
