{- |
Module      :  ./CASL/Qualify.hs
Description :  Code out overloading and qualify all names
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Code out overloading and qualify all names
-}

module CASL.Qualify
  ( qualifySig
  , qualifySigExt
  , inverseMorphism
  ) where

import CASL.AS_Basic_CASL
import CASL.Disambiguate
import CASL.Sign
import CASL.Morphism
import CASL.Monoton

import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result
import qualified Common.Lib.MapSet as MapSet

import Control.Monad
import qualified Control.Monad.Fail as Fail
import qualified Data.Map as Map
import qualified Data.Set as Set

mkOrReuseQualSortName :: Sort_map -> SIMPLE_ID -> LibName -> Id -> Id
mkOrReuseQualSortName sm nodeId libId i =
  case Map.lookup i sm of
    Just j | isQualName j -> j
    _ -> mkQualName nodeId libId i

qualifySig :: SIMPLE_ID -> LibName -> Morphism f e () -> Sign f e
           -> Result (Morphism f e (), [Named (FORMULA f)])
qualifySig = qualifySigExt (\ _ _ _ _ -> extendedInfo) ()

qualifySigExt :: InducedSign f e m e -> m -> SIMPLE_ID -> LibName
              -> Morphism f e m -> Sign f e
              -> Result (Morphism f e m, [Named (FORMULA f)])
qualifySigExt extInd extEm nodeId libId m sig = do
  let ps = predMap sig
      os = opMap sig
      ss = sortSet sig
      sm = Set.fold (\ s -> Map.insert s
                    $ mkOrReuseQualSortName (sort_map m) nodeId libId s)
           Map.empty ss
      sMap = Set.fold (`Map.insert` 1) Map.empty ss
      om = createOpMorMap $ qualOverloaded sMap (Map.map fst $ op_map m)
           nodeId libId (mapOpType sm) mkPartial os
      oMap = Map.foldrWithKey (\ i ->
             Map.insertWith (+) i . Set.size) sMap $ MapSet.toMap os
      pm = Map.map fst $ qualOverloaded oMap (pred_map m) nodeId libId
           (mapPredType sm) id ps
  return ((embedMorphism extEm sig $ inducedSignAux extInd sm om pm extEm sig)
    { sort_map = sm
    , op_map = om
    , pred_map = pm }, monotonicities sig)

qualOverloaded :: Ord a => Map.Map Id Int -> Map.Map (Id, a) Id -> SIMPLE_ID
               -> LibName -> (a -> a) -> (a -> a) -> MapSet.MapSet Id a
               -> Map.Map (Id, a) (Id, a)
qualOverloaded oMap rn nodeId libId f g =
  Map.foldrWithKey (\ i s m -> foldr (\ (e, n) -> let ge = g e in
    Map.insert (i, ge)
      (case Map.lookup (i, ge) rn of
         Just j | isQualName j -> j
         _ -> mkQualName nodeId libId $ mkOverloadedId n i, f e)) m
                  $ zip (Set.toList s) [1 + Map.findWithDefault 0 i oMap ..])
    Map.empty . MapSet.toMap

inverseMorphism :: (Morphism f e m -> Result m) -> Morphism f e m
  -> Result (Morphism f e m)
inverseMorphism invExt m = do
  iExt <- invExt m
  let src = msource m
      ss = sortSet src
      os = opMap src
      ps = predMap src
      sm = sort_map m
      om = op_map m
      pm = pred_map m
      ism = Map.fromList $ map (\ (s1, s2) -> (s2, s1)) $ Map.toList sm
      iom = Map.fromList $ map (\ ((i, t), (j, k)) ->
                  ((j, mapOpType sm t), (i, k))) $ Map.toList om
      ipm = Map.fromList $ map (\ ((i, t), j) ->
                  ((j, mapPredType sm t), i)) $ Map.toList pm
  unless (ss == Set.map (mapSort ism . mapSort sm) ss)
    $ Fail.fail "no injective CASL sort mapping"
  unless (os == inducedOpMap ism iom (inducedOpMap sm om os))
    $ Fail.fail "no injective CASL op mapping"
  unless (ps == inducedPredMap ism ipm (inducedPredMap sm pm ps))
    $ Fail.fail "no injective CASL pred mapping"
  return (embedMorphism iExt (imageOfMorphism m) src)
    { sort_map = ism
    , op_map = iom
    , pred_map = ipm }
