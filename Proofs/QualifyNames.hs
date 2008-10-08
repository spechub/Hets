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

import Proofs.EdgeUtils

import Logic.Coerce
import Logic.Comorphism
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

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
    G_theory lid (ExtSign sig _) _ sens _ -> do
        hins <- foldM (\ l (GMorphism cid _ _ mor _) ->
            if isIdComorphism (Comorphism cid) && language_name lid ==
               language_name (targetLogic cid) then do
                hmor <- coerceMorphism (targetLogic cid) lid
                        "qualifyLabNode" mor
                return $ hmor : l
            else return l) [] $ map (\ (_, _, ld) -> dgl_morphism ld) inss
        (m1, osens) <- qualify lid (mkSimpleId $ getDGNodeName lb)
                          (getLIB_ID ln) hins sig
        rm <- inverse m1
        nThSens <- mapThSensValueM (map_sen lid m1) sens
        let nlb = lb { dgn_theory = G_theory lid
             (makeExtSign lid (cod m1)) startSigId
             (joinSens nThSens $ toThSens osens) startThId }
        ninss <- mapM (composeWithMorphism True $ G_morphism lid m1 startMorId)
          inss
        nouts <- mapM (composeWithMorphism False $ G_morphism lid rm startMorId)
          outs
        let changes = map DeleteEdge (outs ++ inss)
              ++ SetNodeLab lb (n, nlb) : map InsertEdge (ninss ++ nouts)
        return (changesDG dg changes, le)

composeWithMorphism :: Bool -> G_morphism -> LEdge DGLinkLab
                    -> Result (LEdge DGLinkLab)
composeWithMorphism dir mor (s, t, lb) = do
    nmor <- (if dir then id else flip) comp (dgl_morphism lb) $ gEmbed mor
    return (s, t, lb { dgl_morphism = nmor})
