{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Modal/ModalSign.hs
Copyright   :  (c) Till Mossakowski, C. Maeder, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signatures for modal logic, as extension of CASL signatures.
-}

module Modal.ModalSign where

import Modal.AS_Modal

import CASL.Sign

import qualified Common.Lib.MapSet as MapSet
import Common.Id

import Data.Data
import qualified Data.List as List
import qualified Data.HashMap.Strict as Map

import Data.Hashable

data ModalSign = ModalSign
  { flexOps :: OpMap
  , flexPreds :: PredMap
  , modies :: Map.HashMap SIMPLE_ID [AnModFORM]
  , termModies :: Map.HashMap Id [AnModFORM] -- SORT
  } deriving (Show, Eq, Ord, Typeable, Data)

emptyModalSign :: ModalSign
emptyModalSign = ModalSign MapSet.empty MapSet.empty Map.empty Map.empty

addModalSign :: ModalSign -> ModalSign -> ModalSign
addModalSign a b = a
  { flexOps = addOpMapSet (flexOps a) $ flexOps b
  , flexPreds = addMapSet (flexPreds a) $ flexPreds b
  , modies = Map.unionWith List.union (modies a) $ modies b
  , termModies = Map.unionWith List.union (termModies a) $ termModies b }

interMap :: (Ord a, Hashable a) => ([b] -> [b] -> [b]) -> Map.HashMap a [b] -> Map.HashMap a [b]
         -> Map.HashMap a [b]
interMap f m = Map.filter (not . null) . Map.intersectionWith f m

interModalSign :: ModalSign -> ModalSign -> ModalSign
interModalSign a b = a
  { flexOps = interOpMapSet (flexOps a) $ flexOps b
  , flexPreds = interMapSet (flexPreds a) $ flexPreds b
  , modies = interMap List.intersect (modies a) $ modies b
  , termModies = interMap List.intersect (termModies a) $ termModies b }

diffModalSign :: ModalSign -> ModalSign -> ModalSign
diffModalSign a b = a
  { flexOps = diffOpMapSet (flexOps a) $ flexOps b
  , flexPreds = diffMapSet (flexPreds a) $ flexPreds b
  , modies = Map.differenceWith diffList (modies a) $ modies b
  , termModies = Map.differenceWith diffList (termModies a) $ termModies b
  } where diffList c d = let e = c List.\\ d in
            if null e then Nothing else Just e

isSubModalSign :: ModalSign -> ModalSign -> Bool
isSubModalSign a b =
    isSubOpMap (flexOps a) (flexOps b)
    && isSubMap (flexPreds a) (flexPreds b)
    && Map.isSubmapOfBy sublist (modies a) (modies b)
    && Map.isSubmapOfBy sublist (termModies a) (termModies b)
    where sublist l1 l2 = List.union l2 l1 == l2
