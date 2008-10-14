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

mkOrReuseQualSortName :: Sort_map -> SIMPLE_ID -> LIB_ID -> Id -> Id
mkOrReuseQualSortName sm nodeId libId i =
  case Map.lookup i sm of
    Just j | isQualName j -> j
    _ -> mkQualName nodeId libId i

qualifySig :: SIMPLE_ID -> LIB_ID -> Morphism f e () -> Sign f e
           -> Result (Morphism f e (), [Named (FORMULA f)])
qualifySig nodeId libId m sig = do
  let ps = predMap sig
      os = opMap sig
      ss = sortSet sig
      sm = Set.fold (\ s -> Map.insert s
                    $ mkOrReuseQualSortName (sort_map m) nodeId libId s)
           Map.empty ss
      om = createFunMap $ qualOverloaded (Map.map fst $ fun_map m)
           nodeId libId (mapOpType sm) (\ o -> o { opKind = Partial }) os
      pm = Map.map fst
           $ qualOverloaded (pred_map m) nodeId libId (mapPredType sm) id ps
      tar = sig
        { sortSet = Set.map (mapSort sm) ss
        , sortRel = Rel.map (mapSort sm) $ sortRel sig
        , emptySortSet = Set.map (mapSort sm) $ emptySortSet sig
        , opMap = inducedOpMap sm om os
        , assocOps = inducedOpMap sm om $ assocOps sig
        , predMap = inducedPredMap sm pm ps }
  return ((embedMorphism () sig tar)
    { sort_map = sm
    , fun_map = om
    , pred_map = pm }, monotonicities sig)

qualOverloaded :: Ord a => Map.Map (Id, a) Id -> SIMPLE_ID -> LIB_ID
               -> (a -> a) -> (a -> a) -> Map.Map Id (Set.Set a)
               -> Map.Map (Id, a) (Id, a)
qualOverloaded rn nodeId libId f g =
  Map.foldWithKey (\ i s m -> case Set.toList s of
      [] -> error "CASL.Qualify.qualOverloaded"
      t : r -> let
        gt = g t
        m1 = Map.insert (i, gt) (case Map.lookup (i, gt) rn of
                          Just j | isQualName j -> j
                          _ -> mkQualName nodeId libId i, f t) m
       in foldr (\ (e, n) -> let ge = g e in Map.insert (i, ge)
                 (case Map.lookup (i, ge) rn of
                    Just j | isQualName j -> j
                    _ -> mkQualName nodeId libId $ mkOverloadedId n i, f e)) m1
           $ zip r [2 ..]) Map.empty

createFunMap :: Map.Map (Id, OpType) (Id, OpType)
             -> Map.Map (Id, OpType) (Id, FunKind)
createFunMap = Map.map (\ (i, t) -> (i, opKind t))

inverseMorphism :: (m -> Result m) -> Morphism f e m -> Result (Morphism f e m)
inverseMorphism invExt m = do
  iExt <- invExt $ extended_map m
  let src = msource m
      ss = sortSet src
      os = opMap src
      ps = predMap src
      tar = mtarget m
      sm = sort_map m
      nss = Set.map (mapSort sm) ss
      nos = inducedOpMap sm fm os
      nps = inducedPredMap sm pm ps
      fm = fun_map m
      pm = pred_map m
      ntar = tar
        { sortSet = nss
        , sortRel = Rel.map (mapSort sm) $ sortRel src
        , emptySortSet = Set.map (mapSort sm) $ emptySortSet src
        , opMap = nos
        , assocOps = inducedOpMap sm fm $ assocOps src
        , predMap = nps }
      ism = Map.fromList $ map (\ (s1, s2) -> (s2, s1)) $ Map.toList sm
      ifm = Map.fromList $ map (\ ((i, t), (j, k)) ->
                  ((j, mapOpType sm t), (i, k))) $ Map.toList fm
      ipm = Map.fromList $ map (\ ((i, t), j) ->
                  ((j, mapPredType sm t), i)) $ Map.toList pm
  unless (ss == Set.map (mapSort ism) nss)
    $ fail "no injective CASL sort mapping"
  unless (os == inducedOpMap ism ifm nos)
    $ fail "no injective CASL op mapping"
  unless (ps == inducedPredMap ism ipm nps)
    $ fail "no injective CASL pred mapping"
  return (embedMorphism iExt ntar src)
    { sort_map = ism
    , fun_map = ifm
    , pred_map = ipm }
