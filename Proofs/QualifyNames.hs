{- |
Module      :  $Header$
Description :  qualify all names in the nodes of development graphs
Copyright   :  (c) Igor Stassiy, C.Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

qualify and disambiguate all names in the nodes of a development graph for
OMDoc output or for writing out multiple theories for Isabelle or VSE.  Note
however that signature will be always be complete, i.e. imported entities
will be repeated.
-}

module Proofs.QualifyNames where

import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic

import Static.DevGraph
import Static.GTheory

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import Control.Monad

foldWithKeyM :: Monad m => (k -> v -> a -> m a) -> a -> Map.Map k v -> m a
foldWithKeyM f a = foldM (flip $ uncurry f) a . Map.toList

qualifyLibEnv :: LibEnv -> Result LibEnv
qualifyLibEnv le = foldWithKeyM qualifyDGraph le le

qualifyDGraph :: LIB_NAME -> DGraph -> LibEnv -> Result LibEnv
qualifyDGraph ln dg le = do
  (dg1, le1) <- foldM (uncurry $ qualifyLabNode ln) (dg, le) $ labNodesDG dg
  return $ Map.insert ln dg1 le1

qualifyLabNode :: LIB_NAME -> DGraph -> LibEnv -> LNode DGNodeLab
               -> Result (DGraph, LibEnv)
qualifyLabNode ln dg le (n, lb) = let
  inss = innDG dg n
  outs = outDG dg n in
  case dgn_theory lb of
    G_theory lid (ExtSign sig syms) sigId sens thId -> do
        hins <- foldM (\ l (GMorphism cid s sid mor morId) ->
            if isIdComorphism (Comorphism cid) && language_name lid ==
               language_name (targetLogic cid) then do
                hmor <- coerceMorphism (targetLogic cid) lid
                        "qualifyLabNode" mor
                return $ hmor : l
            else return l) [] $ map (\ (_, _, ld) -> dgl_morphism ld) inss
        (m1, osens) <- qualify lid (mkSimpleId $ getDGNodeName lb)
                          (getLIB_ID ln) hins sig
        -- compose morphisms with in- and out- going edges
        -- later, keep or merge renamings of ingoing edges
        return (dg, le)
