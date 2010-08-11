{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, C. Maeder, Uni Bremen 2004
License     :  GPLv2 or higher

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signatures for modal logic, as extension of CASL signatures.
-}

module Modal.ModalSign where

import CASL.Sign
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Id
import Modal.AS_Modal
import qualified Data.List as List

data ModalSign = ModalSign
  { rigidOps :: OpMap
  , rigidPreds :: Map.Map Id (Set.Set PredType)
  , modies :: Map.Map SIMPLE_ID [AnModFORM]
  , termModies :: Map.Map Id [AnModFORM] --SORT
  } deriving (Show, Eq, Ord)

emptyModalSign :: ModalSign
emptyModalSign = ModalSign Map.empty Map.empty Map.empty Map.empty

addModalSign :: ModalSign -> ModalSign -> ModalSign
addModalSign a b = a
  { rigidOps = addOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = addMapSet (rigidPreds a) $ rigidPreds b
  , modies = Map.unionWith  List.union (modies a) $ modies b
  , termModies = Map.unionWith List.union (termModies a) $ termModies b }

interMap :: Ord a => ([b] -> [b] -> [b]) -> Map.Map a [b] -> Map.Map a [b]
         -> Map.Map a [b]
interMap f m = Map.filter (not . null) . Map.intersectionWith f m

interModalSign :: ModalSign -> ModalSign -> ModalSign
interModalSign a b = a
  { rigidOps = interOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = interMapSet (rigidPreds a) $ rigidPreds b
  , modies = interMap List.intersect (modies a) $ modies b
  , termModies = interMap List.intersect (termModies a) $ termModies b }

diffModalSign :: ModalSign -> ModalSign -> ModalSign
diffModalSign a b = a
  { rigidOps = diffMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = diffMapSet (rigidPreds a) $ rigidPreds b
  , modies = Map.differenceWith diffList (modies a) $ modies b
  , termModies = Map.differenceWith diffList (termModies a) $ termModies b
  } where diffList c d = let e = c List.\\ d in
            if null e then Nothing else Just e

isSubModalSign :: ModalSign -> ModalSign -> Bool
isSubModalSign a b =
    isSubOpMap (rigidOps a) (rigidOps b)
    && isSubMapSet (rigidPreds a) (rigidPreds b)
    && Map.isSubmapOfBy sublist (modies a) (modies b)
    && Map.isSubmapOfBy sublist (termModies a) (termModies b)
    where sublist l1 l2 = List.union l2 l1 == l2
