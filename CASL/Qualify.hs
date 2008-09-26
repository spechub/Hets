{- |
Module      :  $Header$
Description :  Code out overloading and qualify all names
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Code out overloading and qualify all names
-}

module CASL.Qualify (qualifySig) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Monoton

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result
import qualified Common.InjMap as InjMap

mkOverloadedId :: Int -> Id -> Id
mkOverloadedId n i =
  Id [genToken "Over"] (i : map (stringToId  . (: [])) (show n)) $ posOfId i

qualifySig :: SIMPLE_ID -> LIB_ID -> Sign f e
        -> Result (Morphism f e (), [Named (FORMULA f)], Morphism f e ())
qualifySig nodeId libId sig = let
  ps = predMap sig
  os = opMap sig
  ss = sortSet sig
  es = emptySortSet sig
  ism = Set.fold (\ s -> InjMap.insert s (mkQualName nodeId libId s))
    InjMap.empty ss
  sm = InjMap.getAToB ism
  ns = Set.map (mapSort sm) ss
  nes = Set.map (mapSort sm) es
  iom = qualOverloaded nodeId libId (mapOpType sm) os
  ipm = qualOverloaded nodeId libId (mapPredType sm) ps
  om = createFunMap $ InjMap.getAToB iom
  pm = Map.map fst $ InjMap.getAToB ipm
  rom = createFunMap $ InjMap.getBToA iom
  rpm = Map.map fst $ InjMap.getBToA ipm
  nos = Map.fromList $ map (\ (i, t) -> (i, Set.singleton t)) $ Map.keys rom
  nps = Map.fromList $ map (\ (i, t) -> (i, Set.singleton t)) $ Map.keys rpm
  tar = sig
    { sortSet = ns
    , sortRel = Rel.map (mapSort sm) $ sortRel sig
    , emptySortSet = nes
    , opMap = nos
    , assocOps = Map.empty
    , predMap = nps }
  in return ((embedMorphism () sig tar)
    { sort_map = sm
    , fun_map = om
    , pred_map = pm }
     , monotonicities sig
     , (embedMorphism () tar sig)
    { sort_map = InjMap.getBToA ism
    , fun_map = rom
    , pred_map = rpm })

qualOverloaded :: Ord a => SIMPLE_ID -> LIB_ID -> (a -> a)
               -> Map.Map Id (Set.Set a) -> InjMap.InjMap (Id, a) (Id, a)
qualOverloaded nodeId libId f =
  Map.foldWithKey (\ i s m -> case Set.toList s of
      [] -> error "CASL.Qualify.qualOverloaded"
      t : r -> let m1 = InjMap.insert (i, t) (mkQualName nodeId libId i, f t) m
       in foldr (\ (e, n) -> InjMap.insert (i, e)
                 (mkQualName nodeId libId $ mkOverloadedId n i, f e)) m1
           $ zip r [2 ..]) InjMap.empty

createFunMap :: Map.Map (Id, OpType) (Id, OpType)
             -> Map.Map (Id, OpType) (Id, FunKind)
createFunMap = Map.map (\ (i, t) -> (i, opKind t))
