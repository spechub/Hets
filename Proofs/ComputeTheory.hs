{- |
Module      :  $Header$
Description :  compute the theory of a node
Copyright   :  (c) Christian Maeder and DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute the theory of a node
-}

module Proofs.ComputeTheory
    ( computeTheory
    , computeLabelTheory
    , theoremsToAxioms
    , computeAllTheories
    , computeDGraphTheories
    , globalNodeTheory
    ) where

import Logic.Prover

import Static.GTheory
import Static.DevGraph

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import Data.List (sortBy)
import qualified Data.Map as Map

import Control.Monad

-- | compute the theory of a node, using normal forms when available
computeLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> Result G_theory
computeLabelTheory _libEnv _dg (_n, nodelab) = getGlobalTheory nodelab

computeNodeTheory :: LibEnv -> DGraph -> Node -> Result G_theory
computeNodeTheory libEnv dg n = computeLabelTheory libEnv dg (n, labDG dg n)

computeTheory :: LibEnv -> LibName -> Node -> Result G_theory
computeTheory libEnv ln = computeNodeTheory libEnv $ lookupDGraph ln libEnv

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2

getGlobalTheory :: DGNodeLab -> Result G_theory
getGlobalTheory = maybe (fail "no global theory") return . globalTheory

globalNodeTheory :: DGraph -> Node -> Result G_theory
globalNodeTheory dg = getGlobalTheory . labDG dg

computeAllTheories :: LibEnv -> LibEnv
computeAllTheories libEnv =
  foldl (\ le ln -> Map.adjust (computeDGraphTheories le) ln le) libEnv
    $ getTopsortedLibs libEnv

computeDGraphTheories :: LibEnv -> DGraph -> DGraph
computeDGraphTheories le dgraph =
  foldl (\ dg l@(n, lbl) -> fst $ labelNodeDG (n, lbl
     { globalTheory = maybeResult $ computeLabelTh le dg l }) dg)
     dgraph $ topsortedNodes dgraph

computeLabelTh :: LibEnv -> DGraph -> LNode DGNodeLab -> Result G_theory
computeLabelTh le dg (n, lbl) = let localTh = dgn_theory lbl in
    if isDGRef lbl then do
        let refNode = dgn_node lbl
            dg' = lookupDGraph (dgn_libname lbl) le
            newLab = labDG dg' refNode
        refTh <- getGlobalTheory newLab
        joinG_sentences (theoremsToAxioms refTh) localTh
    else do
      ths <- mapM (\ (s, _, l) -> do
         th <- if isLocalDef $ dgl_type l then
                   computeLocalNodeTheory le dg s
               else globalNodeTheory dg s
         -- translate theory and turn all imported theorems into axioms
         translateG_theory (dgl_morphism l) $ theoremsToAxioms th)
         $ sortBy
            (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1)
            $ filter (liftE $ liftOr isGlobalDef isLocalDef)
            $ innDG dg n
      flatG_sentences localTh ths
