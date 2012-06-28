{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

Signatures for extended modal logic as extension of CASL signatures.
In contrast to theoretical descriptions we keep separate sets of the flexible
operations to ensure that operations i.e. from CASL free types are rigid by default.
-}

module ExtModal.ExtModalSign where

import CASL.Sign

import Common.Id
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

data EModalSign = EModalSign
        { flexOps :: OpMap
        , flexPreds :: PredMap
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
        { flexOps = addOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.union (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.union (modalities ms1) $ modalities ms2
        , time_modalities = Set.union (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.union (termMods ms1) $ termMods ms2
        , nominals = Set.union (nominals ms1) (nominals ms2)
        }

interEModalSign :: EModalSign -> EModalSign -> EModalSign
interEModalSign ms1 ms2 = ms1
        { flexOps = interOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.intersection (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.intersection (modalities ms1) $ modalities ms2
        , time_modalities = Set.intersection (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.intersection (termMods ms1) $ termMods ms2
        , nominals = Set.intersection (nominals ms1) (nominals ms2)
        }

diffEModalSign :: EModalSign -> EModalSign -> EModalSign
diffEModalSign ms1 ms2 = ms1
        { flexOps = diffOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.difference (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.difference (modalities ms1) $ modalities ms2
        , time_modalities = Set.difference (time_modalities ms1)
                            (time_modalities ms2)
        , termMods = Set.difference (termMods ms1) $ termMods ms2
        , nominals = Set.difference (nominals ms1) (nominals ms2)
        } where

isSubEModalSign :: EModalSign -> EModalSign -> Bool
isSubEModalSign ms1 ms2 =
        isSubOpMap (flexOps ms1) (flexOps ms2)
        && MapSet.isSubmapOf (flexPreds ms1) (flexPreds ms2)
        && Set.isSubsetOf (modalities ms1) (modalities ms2)
        && Set.isSubsetOf (time_modalities ms1) (time_modalities ms2)
        && Set.isSubsetOf (termMods ms1) (termMods ms2)
        && Set.isSubsetOf (nominals ms1) (nominals ms2)
