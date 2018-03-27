{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./RigidCASL/Sign.hs
License     :  GPLv2 or higher, see LICENSE.txt

Stability   :  provisional
Portability :  portable

Signatures for hybrid logic, as extension of CASL signatures.
-}

module RigidCASL.Sign where

import CASL.Sign
import qualified CASL.AS_Basic_CASL as CBasic

import qualified Common.Lib.MapSet as MapSet

import Data.Data
import qualified Data.Set as Set


data RigidExt = RigidExt
  { rigidSorts :: Set.Set CBasic.SORT
  , rigidOps :: OpMap
  , rigidPreds :: PredMap
  } deriving (Show, Eq, Ord, Typeable, Data)

type RSign = Sign () RigidExt

emptyRigidExt :: RigidExt
emptyRigidExt = RigidExt Set.empty MapSet.empty MapSet.empty

addRigidExt :: RigidExt -> RigidExt -> RigidExt
addRigidExt a b = a
  { rigidSorts = Set.union (rigidSorts a) $ rigidSorts b
  , rigidOps = addOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = addMapSet (rigidPreds a) $ rigidPreds b
  }

interRigidExt :: RigidExt -> RigidExt -> RigidExt
interRigidExt a b = a
  { rigidSorts = Set.intersection (rigidSorts a) $ rigidSorts b
  , rigidOps = interOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = interMapSet (rigidPreds a) $ rigidPreds b
  }

diffRigidExt :: RigidExt -> RigidExt -> RigidExt
diffRigidExt a b = a
  { rigidSorts = Set.difference (rigidSorts a) $ rigidSorts b
  , rigidOps = diffOpMapSet (rigidOps a) $ rigidOps b
  , rigidPreds = diffMapSet (rigidPreds a) $ rigidPreds b
  }

isSubRigidExt :: RigidExt -> RigidExt -> Bool
isSubRigidExt a b =
       Set.isSubsetOf (rigidSorts a) (rigidSorts b)
    && isSubOpMap (rigidOps a) (rigidOps b)
    && isSubMap (rigidPreds a) (rigidPreds b)

instance SignExtension RigidExt where
    isSubSignExtension = isSubRigidExt  

caslSign :: RSign -> CASLSign
caslSign sig = Sign
    { sortRel = sortRel sig
    , revSortRel = revSortRel sig
    , emptySortSet = emptySortSet sig
    , opMap = opMap sig
    , assocOps = assocOps sig
    , predMap = predMap sig
    , varMap = varMap sig
    , sentences = sentences sig
    , declaredSymbols = declaredSymbols sig
    , envDiags = envDiags sig
    , annoMap = annoMap sig
    , globAnnos = globAnnos sig
    , extendedInfo = ()
    } 

