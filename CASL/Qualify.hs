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

module CASL.Qualify (qualifySig, inverseMorphism) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Monoton

import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set

mkOverloadedId :: Int -> Id -> Id
mkOverloadedId n i =
  Id [genToken "Over"] (i : map (stringToId  . (: [])) (show n)) $ posOfId i

qualifySig :: SIMPLE_ID -> LIB_ID -> [Morphism f e ()] -> Sign f e
           -> Result (Morphism f e (), [Named (FORMULA f)])
qualifySig nodeId libId inns sig = let
  ps = predMap sig
  os = opMap sig
  ss = sortSet sig
  sm = Set.fold (\ s -> Map.insert s (mkQualName nodeId libId s)) Map.empty ss
  om = createFunMap $ qualOverloaded nodeId libId (mapOpType sm) os
  pm = Map.map fst $ qualOverloaded nodeId libId (mapPredType sm) ps
  tar = sig
    { sortSet = Set.map (mapSort sm) ss
    , sortRel = Rel.map (mapSort sm) $ sortRel sig
    , emptySortSet = Set.map (mapSort sm) $ emptySortSet sig
    , opMap = inducedOpMap sm om os
    , assocOps = inducedOpMap sm om $ assocOps sig
    , predMap = inducedPredMap sm pm ps }
  in return ((embedMorphism () sig tar)
    { sort_map = sm
    , fun_map = om
    , pred_map = pm }, monotonicities sig)

qualOverloaded :: Ord a => SIMPLE_ID -> LIB_ID -> (a -> a)
               -> Map.Map Id (Set.Set a) -> Map.Map (Id, a) (Id, a)
qualOverloaded nodeId libId f =
  Map.foldWithKey (\ i s m -> case Set.toList s of
      [] -> error "CASL.Qualify.qualOverloaded"
      t : r -> let m1 = Map.insert (i, t) (mkQualName nodeId libId i, f t) m
       in foldr (\ (e, n) -> Map.insert (i, e)
                 (mkQualName nodeId libId $ mkOverloadedId n i, f e)) m1
           $ zip r [2 ..]) Map.empty

createFunMap :: Map.Map (Id, OpType) (Id, OpType)
             -> Map.Map (Id, OpType) (Id, FunKind)
createFunMap = Map.map (\ (i, t) -> (i, opKind t))

inverseMorphism :: (m -> Result m) -> Morphism f e m -> Result (Morphism f e m)
inverseMorphism invExt m = do
  iExt <- invExt $ extended_map m
  let src = msource m
      tar = mtarget m
      sm = sort_map m
      im = Map.fromList $ map (\ (s1, s2) -> (s2, s1)) $ Map.toList sm
  unless (sortSet tar == Set.map (mapSort sm) (sortSet src))
    $ fail "no injective CASL sort mapping"
  unless (opMap tar == inducedOpMap sm (fun_map m) (opMap src))
    $ fail "no injective CASL op mapping"
  unless (predMap tar == inducedPredMap sm (pred_map m) (predMap src))
    $ fail "no injective CASL pred mapping"
  return (embedMorphism iExt tar src)
    { sort_map = im
    , fun_map = Map.fromList $ map (\ ((i, t), (j, k)) ->
                  ((j, makeTotal k $ mapOpType im t), (i, opKind t)))
               $ Map.toList $ fun_map m
    , pred_map = Map.fromList $ map (\ ((i, t), j) ->
                  ((j, mapPredType im t), i)) $ Map.toList $ pred_map m
    , morKind = if morKind m == IdMor then IdMor else OtherMor }
