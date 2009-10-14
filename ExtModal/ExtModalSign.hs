{- |
Module      :  ./ExtModal/ExtModalSign.hs
Copyright   :  
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  
Stability   :  experimental
Portability :  

Signatures for extended modal logic, as extension of CASL signatures.
-}

module ExtModal.ExtModalSign where

import CASL.Sign
import Common.Id

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set

import ExtModal.AS_ExtModal


data EModalSign = EModalSign
	{ rigidOps :: OpMap
	, rigidPreds :: Map.Map Id (Set.Set PredType)
	, modalities :: Map.Map SIMPLE_ID [AnEModForm] 
	, time_modalities :: Set.Set SIMPLE_ID
	, nominals :: Set.Set SIMPLE_ID
	} deriving (Show, Eq, Ord)


emptyEModalSign :: EModalSign 
emptyEModalSign = EModalSign Map.empty Map.empty Map.empty Set.empty Set.empty

addEModalSign :: EModalSign -> EModalSign -> EModalSign
addEModalSign ms1 ms2 = ms1
	{ rigidOps = addOpMapSet (rigidOps ms1) (rigidOps ms2)
	, rigidPreds = addMapSet (rigidPreds ms1) (rigidPreds ms2)
	, modalities = Map.unionWith List.union (modalities ms1) (modalities ms2)
	, time_modalities = Set.union (time_modalities ms1) (time_modalities ms2)
	, nominals = Set.union (nominals ms1) (nominals ms2)
	}

interEModalSign :: EModalSign -> EModalSign -> EModalSign
interEModalSign ms1 ms2 = ms1
	{ rigidOps = interOpMapSet (rigidOps ms1) (rigidOps ms2)
	, rigidPreds = interMapSet (rigidPreds ms1) (rigidPreds ms2)
	, modalities = Map.filter (not . null) . Map.intersectionWith List.intersect (modalities ms1) $ (modalities ms2)
	, time_modalities = Set.intersection (time_modalities ms1) (time_modalities ms2)
	, nominals = Set.intersection (nominals ms1) (nominals ms2)
	}

diffEModalSign :: EModalSign -> EModalSign -> EModalSign
diffEModalSign ms1 ms2 = ms1
	{ rigidOps = diffOpMapSet (rigidOps ms1) (rigidOps ms2)
	, rigidPreds = diffMapSet (rigidPreds ms1) (rigidPreds ms2)
	, modalities = Map.differenceWith difflist (modalities ms1) (modalities ms2) 
	, time_modalities = Set.difference (time_modalities ms1) (time_modalities ms2)
	, nominals = Set.difference (nominals ms1) (nominals ms2)
	} where difflist l1 l2 = let res = l1 List.\\ l2 in
			if null res then Nothing else Just res

isSubEModalSign :: EModalSign -> EModalSign -> Bool
isSubEModalSign ms1 ms2 = 
	isSubOpMap (rigidOps ms1) (rigidOps ms2)
	&& isSubMapSet (rigidPreds ms1) (rigidPreds ms2)
	&& Map.isSubmapOfBy sublist (modalities ms1) (modalities ms2)
	&& Set.isSubsetOf (time_modalities ms1) (time_modalities ms2)
	&& Set.isSubsetOf (nominals ms1) (nominals ms2)
	where sublist l1 l2 = List.union l1 l2 == l2

