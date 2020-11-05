{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Hybrid/HybridSign.hs
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  provisional
Portability :  portable

Signatures for hybrid logic, as extension of CASL signatures.
-}

module Hybrid.HybridSign where

import Hybrid.AS_Hybrid

import CASL.Sign

import qualified Common.Lib.MapSet as MapSet
import Common.Id

import Data.Data
import qualified Data.List as List
import qualified Data.HashMap.Lazy as Map
import Data.Hashable

data HybridSign = HybridSign
  { rigidOps :: OpMap
  , rigidPreds :: PredMap
  , modies :: Map.HashMap SIMPLE_ID [AnHybFORM]
  , nomies :: Map.HashMap SIMPLE_ID [AnHybFORM]
  , termModies :: Map.HashMap Id [AnHybFORM] -- SORT
  } deriving (Show, Eq, Ord, Typeable, Data)

emptyHybridSign :: HybridSign
emptyHybridSign = HybridSign MapSet.empty MapSet.empty
                             Map.empty Map.empty Map.empty

addHybridSign :: HybridSign -> HybridSign -> HybridSign
addHybridSign a b = a
  { rigidOps = addOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = addMapSet (rigidPreds a) $ rigidPreds b
  , modies = Map.unionWith List.union (modies a) $ modies b
  , nomies = Map.unionWith List.union (nomies a) (nomies b)
  , termModies = Map.unionWith List.union (termModies a) $ termModies b }

interMap :: (Ord a, Hashable a) => ([b] -> [b] -> [b]) -> Map.HashMap a [b] -> Map.HashMap a [b]
         -> Map.HashMap a [b]
interMap f m = Map.filter (not . null) . Map.intersectionWith f m

interHybridSign :: HybridSign -> HybridSign -> HybridSign
interHybridSign a b = a
  { rigidOps = interOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = interMapSet (rigidPreds a) $ rigidPreds b
  , modies = interMap List.intersect (modies a) $ modies b
  , nomies = interMap List.intersect (nomies a) (nomies b)
  , termModies = interMap List.intersect (termModies a) $ termModies b }

diffHybridSign :: HybridSign -> HybridSign -> HybridSign
diffHybridSign a b = a
  { rigidOps = diffOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = diffMapSet (rigidPreds a) $ rigidPreds b
  , modies = Map.differenceWith diffList (modies a) $ modies b
  , nomies = Map.differenceWith diffList (nomies a) (nomies b)
  , termModies = Map.differenceWith diffList (termModies a) $ termModies b
  } where
     diffList c d = let e = c List.\\ d in
                    if null e then Nothing else Just e

isSubHybridSign :: HybridSign -> HybridSign -> Bool
isSubHybridSign a b =
    isSubOpMap (rigidOps a) (rigidOps b)
    && isSubMap (rigidPreds a) (rigidPreds b)
    && Map.isSubmapOfBy sublist (modies a) (modies b)
    && Map.isSubmapOfBy sublist (nomies a) (nomies b)
    && Map.isSubmapOfBy sublist (termModies a) (termModies b)
    where sublist l1 l2 = List.union l2 l1 == l2
