{- |
Module      :  ./CASL/Disambiguate.hs
Description :  disambiguate all names
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Disambiguate all names that are not in the overload relation for CASL2OWL
-}

module CASL.Disambiguate where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Overload

import Common.Id
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import qualified Data.Set as Set

mkOverloadedId :: Int -> Id -> Id
mkOverloadedId n i@(Id ts cs rs) = if n <= 1 then i else
  Id (ts ++ [mkSimpleId $ '_' : shows n "o"]) cs rs

disambigSig :: Sign f e -> Morphism f e ()
disambigSig = disambigSigExt (\ _ _ _ _ -> extendedInfo) ()

-- note that op-type keys are always partial!
disambigSigExt :: InducedSign f e m e -> m -> Sign f e -> Morphism f e m
disambigSigExt extInd extEm sig =
  let ps = Map.map (Rel.partSet $ leqP sig) $ MapSet.toMap $ predMap sig
      os = Map.map (Rel.partSet $ leqF sig) $ MapSet.toMap $ opMap sig
      ss = sortSet sig
      sMap = Set.fold (`Map.insert` 1) Map.empty ss
      om = createOpMorMap $ disambOverloaded sMap mkPartial os
      oMap = Map.foldrWithKey (\ i ->
             Map.insertWith (+) i . length) sMap os
      pm = Map.map fst $ disambOverloaded oMap id ps
  in (embedMorphism extEm sig $ inducedSignAux extInd Map.empty om pm extEm sig)
    { op_map = om
    , pred_map = pm }

disambOverloaded :: Ord a => Map.Map Id Int
               -> (a -> a)
               -> Map.Map Id [Set.Set a]
               -> Map.Map (Id, a) (Id, a)
disambOverloaded oMap g =
  Map.foldrWithKey (\ i l m ->
    foldr (\ (s, n) m2 -> let j = mkOverloadedId n i in
      Set.fold (\ t -> Map.insert (i, g t) (j, t)) m2 s) m
    $ zip l [1 + Map.findWithDefault 0 i oMap ..])
    Map.empty

createOpMorMap :: Map.Map (Id, OpType) (Id, OpType)
             -> Map.Map (Id, OpType) (Id, OpKind)
createOpMorMap = Map.map (\ (i, t) -> (i, opKind t))
