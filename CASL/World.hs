{- |
Module      :  ./CASL/World.hs
Description :  adding a parameter to ops and preds
Copyright   :  (c) Christian Maeder, DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

add a parameter like the world sort for Modal CASL
-}

module CASL.World where

import Common.Id
import qualified Common.Lib.MapSet as MapSet

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

import qualified Data.Map as Map
import qualified Data.Set as Set

world :: SORT
world = genName "World"

{- | mixfix identifiers need to be extended by a further place holder.  That
is, identifiers are renamed, although a wrong number of place holders would
allow to use the prefix notation. To avoid a name clashes with existing names
the first place holder is preceded by a further place holder and a generated
token. -}
addPlace :: Id -> Id
addPlace i@(Id ts ids ps)
    | isMixfix i = Id ((\ (x, y) -> x ++ placeTok : genToken "W" : y)
                          (break isPlace ts)) ids ps
    | otherwise = i

-- | the changed mapping
addWorld :: Ord a => (a -> a) -> (Id -> Id) -> MapSet.MapSet Id a
  -> MapSet.MapSet Id a
addWorld f ren =
  MapSet.fromMap . Map.mapKeys ren . MapSet.toMap . MapSet.map f

worldOpType :: SORT -> OpType -> OpType
worldOpType ws t = t { opArgs = ws : opArgs t}

-- | the changed op map
addWorldOp :: SORT -> (Id -> Id) -> OpMap -> OpMap
addWorldOp = addWorld . worldOpType

worldPredType :: SORT -> PredType -> PredType
worldPredType ws t = t { predArgs = ws : predArgs t}

-- | the changed pred map
addWorldPred :: SORT -> (Id -> Id) -> PredMap -> PredMap
addWorldPred = addWorld . worldPredType

-- | create a predicate name for time, simple and term modalities
relOfMod :: Bool -> Bool -> SORT -> Id
relOfMod time term m = let s = if time then "T" else "R" in
  Id [genToken $ if term then s ++ "_t" else s] [m] $ rangeOfId m

-- | create a predicate name for simple and term modalities
relName :: Bool -> SORT -> Id
relName = relOfMod False

-- | insert a simple or term modality
insertModPred :: SORT -> Bool -> Bool -> Id -> PredMap -> PredMap
insertModPred ws time term m = MapSet.insert (relOfMod time term m)
   $ modPredType ws term m

modPredType :: SORT -> Bool -> SORT -> PredType
modPredType ws term m = PredType $ (if term then (m :) else id) [ws, ws]

-- | the renaming as part of a morphism
renMorphism :: Ord a => (Id -> Id) -> MapSet.MapSet Id a -> Map.Map (Id, a) Id
renMorphism ren = Map.foldWithKey (\ i s ->
   let j = ren i in
   if j == i then id else
       Map.union . Map.fromAscList . map (\ a -> ((j, a), j)) $ Set.toList s)
   Map.empty . MapSet.toMap

renOpMorphism :: (Id -> Id) -> OpMap -> Op_map
renOpMorphism ren = Map.mapWithKey (\ (_, t) i -> (i, opKind t))
  . renMorphism ren

renPredMorphism :: (Id -> Id) -> PredMap -> Pred_map
renPredMorphism = renMorphism
