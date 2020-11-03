{- |
Module      :  ./CASL/Cycle.hs
Description :  removing sort cycles
Copyright   :  (c) Christian Maeder, DFKI GmbH 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

removing sort cycles
-}

module CASL.Cycle where

import CASL.Sign
import CASL.Morphism

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

removeSortCycles :: Sign f e -> (Sign f e, Sort_map)
removeSortCycles sign = let
   rel = sortRel sign
   cs = Rel.sccOfClosure rel
   mc = foldr ((\ (a, s) m -> Set.fold (`Map.insert` a) m s)
               . Set.deleteFindMin) Map.empty cs
   in (sign
       { sortRel = Rel.irreflex $ Rel.collaps cs rel
       , emptySortSet = Set.map (mapSort mc) $ emptySortSet sign
       , opMap = MapSet.map (mapOpType mc) $ opMap sign
       , predMap = MapSet.map (mapPredType mc) $ predMap sign
       }, mc)
