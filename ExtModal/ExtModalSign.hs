{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

Signatures for extended modal logic, as extension of CASL signatures.
-}

module ExtModal.ExtModalSign where

import CASL.Sign

import Common.Id
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

data EModalSign = EModalSign
        { rigidOps :: OpMap
        , rigidPreds :: PredMap
        , modalities :: Set.Set Id -- do not store sentences in signature
        , time_modalities :: Set.Set Id
        , termMods :: Set.Set Id -- sorts that need to be mapped
        , nominals :: Set.Set SIMPLE_ID
        } deriving (Show, Eq, Ord)

emptyEModalSign :: EModalSign
emptyEModalSign =
  EModalSign MapSet.empty MapSet.empty Set.empty Set.empty Set.empty Set.empty

addEModalSign :: EModalSign -> EModalSign -> EModalSign
addEModalSign ms1 ms2 = ms1
        { rigidOps = addOpMapSet (rigidOps ms1) (rigidOps ms2)
        , rigidPreds = MapSet.union (rigidPreds ms1) (rigidPreds ms2)
        , modalities = Set.union (modalities ms1) $ modalities ms2
        , time_modalities = Set.union (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.union (termMods ms1) $ termMods ms2
        , nominals = Set.union (nominals ms1) (nominals ms2)
        }

interEModalSign :: EModalSign -> EModalSign -> EModalSign
interEModalSign ms1 ms2 = ms1
        { rigidOps = interOpMapSet (rigidOps ms1) (rigidOps ms2)
        , rigidPreds = MapSet.intersection (rigidPreds ms1) (rigidPreds ms2)
        , modalities = Set.intersection (modalities ms1) $ modalities ms2
        , time_modalities = Set.intersection (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.intersection (termMods ms1) $ termMods ms2
        , nominals = Set.intersection (nominals ms1) (nominals ms2)
        }

diffEModalSign :: EModalSign -> EModalSign -> EModalSign
diffEModalSign ms1 ms2 = ms1
        { rigidOps = diffOpMapSet (rigidOps ms1) (rigidOps ms2)
        , rigidPreds = MapSet.difference (rigidPreds ms1) (rigidPreds ms2)
        , modalities = Set.difference (modalities ms1) $ modalities ms2
        , time_modalities = Set.difference (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.difference (termMods ms1) $ termMods ms2
        , nominals = Set.difference (nominals ms1) (nominals ms2)
        } where

isSubEModalSign :: EModalSign -> EModalSign -> Bool
isSubEModalSign ms1 ms2 =
        isSubOpMap (rigidOps ms1) (rigidOps ms2)
        && MapSet.isSubmapOf (rigidPreds ms1) (rigidPreds ms2)
        && Set.isSubsetOf (modalities ms1) (modalities ms2)
        && Set.isSubsetOf (time_modalities ms1) (time_modalities ms2)
        && Set.isSubsetOf (termMods ms1) (termMods ms2)
        && Set.isSubsetOf (nominals ms1) (nominals ms2)
