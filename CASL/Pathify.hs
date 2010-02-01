{- |
Module      :  $Header$
Description :  Pathify all names
Copyright   :  (c) Ewaryst Schulz, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

Pathify all signature names
-}

module CASL.Pathify
  ( pathifyNames
  ) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

import Common.Id
import Common.LibName
import Common.Result

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Graph.Inductive.Graph

{-
idToSortSymbol :: Id -> Symbol
idToOpSymbol :: Id -> OpType -> Symbol
idToPredSymbol :: Id -> PredType -> Symbol





  sortM <- foldM (pathifySort libid sig l) Map.empty $ Set.toList $ sortSet sig
  opM <- foldM (pathifyOp libid sig l) sortM $ flattenOpMap $ opMap sig
  foldM (pathifyPred libid sig l) opM $ flattenPredMap $ predMap sig

-}


pathifyNames :: (Show f, Show e) => LibId -> Sign f e
             -> [(Node, Morphism f e m, Bool, Map.Map Symbol [LinkPath Symbol])]
             -> Result (Map.Map Symbol [LinkPath Symbol])
pathifyNames libid sig l = do
  let initial = Map.fromList
                $ map (\ i -> (idToSortSymbol i,[]))
                      (Set.toList $ sortSet sig)
                ++  map (\ (i,ot) -> (idToOpSymbol i ot,[]))
                        (flattenOpMap $ opMap sig)
                ++  map (\ (i,pt) -> (idToPredSymbol i pt,[]))
                        (flattenPredMap $ predMap sig)
  warning () ("pathifyNames, SIG: " ++ show sig) nullRange
  foldM (pathifyImport libid) initial l


pathifyImport :: LibId -> Map.Map Symbol [LinkPath Symbol]
              -> (Node, Morphism f e m, Bool, Map.Map Symbol [LinkPath Symbol])
              -> Result (Map.Map Symbol [LinkPath Symbol])

pathifyImport libid lpm0 (n, m, b, lpm) =
    let map4s = mapSort (sort_map m)
        map4o = mapOpSym (sort_map m) (op_map m)
        map4p = mapPredSym (sort_map m) (pred_map m)
        i2ss = idToSortSymbol
        i2os = uncurry idToOpSymbol
        i2ps = uncurry idToPredSymbol
        mkPair x y = if b then (y,x) else (x,y)
        sig = msource m
        symbMap = map (\ i -> let i0 = map4s i in
                              mkPair (i2ss i) $ i2ss i0)
                      (Set.toList $ sortSet sig)
                  ++  map (\ i -> let i0 = map4o i in
                                  mkPair (i2os i) $ i2os i0)
                          (flattenOpMap $ opMap sig)
                  ++  map (\ i -> let i0 = map4p i in
                                  mkPair (i2ps i) $ i2ps i0)
                          (flattenPredMap $ predMap sig)
    in foldM (pathifySymbol libid n lpm) lpm0 symbMap

pathifySymbol :: LibId -> Node -> Map.Map Symbol [LinkPath Symbol]
              -> Map.Map Symbol [LinkPath Symbol] -> (Symbol, Symbol)
              -> Result (Map.Map Symbol [LinkPath Symbol])

pathifySymbol libid n lpm lpm0 (s, sMapped) = do
  -- get the pathslist for the mapped symbol
  let lp0 = lpm0 Map.! sMapped
  -- get the entries in the linksource to add the current path
  let lp = lpm Map.! s
  let lpNew = lp0 ++ if null lp then [initPath libid n sMapped]
                     else map (addToPath libid n) lp
  return $ Map.adjust (const lpNew) sMapped lpm0

{-
getSortPathList libid (n, m, b, pl) s sig = do
  -- 1. check the direction of morphism
  let sourcesig = if b then mtarget m else msource m
  -- 2. lookup the s in the morphism table
  
  -- 3. if not found lookup the s in the source sig
  -- 4. if found somewhere add the n to the paths and return the pathlist
-}

pathifySort :: LibId -> Sign f e
             -> [(Node, Morphism f e m, Bool, Map.Map Symbol [LinkPath Symbol])]
             -> Map.Map Symbol [LinkPath Symbol] -> SORT
             -> Result (Map.Map Symbol [LinkPath Symbol])
pathifySort li sig l m s = return m

pathifyOp :: LibId -> Sign f e
             -> [(Node, Morphism f e m, Bool, Map.Map Symbol [LinkPath Symbol])]
             -> Map.Map Symbol [LinkPath Symbol] -> (Id, OpType)
             -> Result (Map.Map Symbol [LinkPath Symbol])
pathifyOp li sig l m s = return m

pathifyPred :: LibId -> Sign f e
             -> [(Node, Morphism f e m, Bool, Map.Map Symbol [LinkPath Symbol])]
             -> Map.Map Symbol [LinkPath Symbol] -> (Id, PredType)
             -> Result (Map.Map Symbol [LinkPath Symbol])

pathifyPred li sig l m s = return m

