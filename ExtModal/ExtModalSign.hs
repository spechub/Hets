{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./ExtModal/ExtModalSign.hs
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

Signatures for extended modal logic as extension of CASL signatures.
In contrast to theoretical descriptions we keep separate sets of the flexible
operations to ensure that operations i.e. from CASL free types are rigid
by default.
-}

module ExtModal.ExtModalSign where

import CASL.Sign

import Common.Id
import qualified Common.Lib.MapSet as MapSet

import Data.Data
import qualified Data.HashSet as Set

data EModalSign = EModalSign
        { flexOps :: OpMap
        , flexPreds :: PredMap
        , modalities :: Set.HashSet Id -- do not store sentences in signature
        , timeMods :: Set.HashSet Id
        , termMods :: Set.HashSet Id -- sorts that need to be mapped
        , nominals :: Set.HashSet Id
        } deriving (Show, Eq, Ord, Typeable, Data)

nomPType :: PredType
nomPType = PredType []

nomPId :: Token -> Id
nomPId t = mkId [t]

correctSign :: Sign f EModalSign -> Sign f EModalSign
correctSign s = let e = extendedInfo s in
  s { extendedInfo = e
      { flexOps = interOpMapSet (flexOps e) $ opMap s
      , flexPreds = interMapSet (flexPreds e) $ predMap s }}

emptyEModalSign :: EModalSign
emptyEModalSign =
  EModalSign MapSet.empty MapSet.empty Set.empty Set.empty Set.empty Set.empty

addEModalSign :: EModalSign -> EModalSign -> EModalSign
addEModalSign ms1 ms2 = ms1
        { flexOps = addOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.union (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.union (modalities ms1) $ modalities ms2
        , timeMods = Set.union (timeMods ms1)
                            (timeMods ms2)
        , termMods = Set.union (termMods ms1) $ termMods ms2
        , nominals = Set.union (nominals ms1) (nominals ms2)
        }

interEModalSign :: EModalSign -> EModalSign -> EModalSign
interEModalSign ms1 ms2 = ms1
        { flexOps = interOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.intersection (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.intersection (modalities ms1) $ modalities ms2
        , timeMods = Set.intersection (timeMods ms1)
                            (timeMods ms2)
        , termMods = Set.intersection (termMods ms1) $ termMods ms2
        , nominals = Set.intersection (nominals ms1) (nominals ms2)
        }

diffEModalSign :: EModalSign -> EModalSign -> EModalSign
diffEModalSign ms1 ms2 = ms1
        { flexOps = diffOpMapSet (flexOps ms1) (flexOps ms2)
        , flexPreds = MapSet.difference (flexPreds ms1) (flexPreds ms2)
        , modalities = Set.difference (modalities ms1) $ modalities ms2
        , timeMods = Set.difference (timeMods ms1)
                            (timeMods ms2)
        , termMods = Set.difference (termMods ms1) $ termMods ms2
        , nominals = Set.difference (nominals ms1) (nominals ms2)
        } where

isSubEModalSign :: EModalSign -> EModalSign -> Bool
isSubEModalSign ms1 ms2 =
        isSubOpMap (flexOps ms1) (flexOps ms2)
        && MapSet.isSubmapOf (flexPreds ms1) (flexPreds ms2)
        && Set.isSubsetOf (modalities ms1) (modalities ms2)
        && Set.isSubsetOf (timeMods ms1) (timeMods ms2)
        && Set.isSubsetOf (termMods ms1) (termMods ms2)
        && Set.isSubsetOf (nominals ms1) (nominals ms2)
