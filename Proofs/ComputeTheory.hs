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
    ) where

import Logic.Prover

import Static.GTheory
import Static.DevGraph

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import Data.List (sortBy)
import Control.Monad

-- | compute the theory of a node, using normal forms when available
computeLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> Result G_theory
computeLabelTheory libEnv dg (n, nodelab) =
  let localTh = dgn_theory nodelab in
  if isDGRef nodelab then do
    let refNode = dgn_node nodelab
        dg' = lookupDGraph (dgn_libname nodelab) libEnv
        newLab = labDG dg' refNode
    refTh <- computeLabelTheory libEnv dg' (refNode, newLab)
    joinG_sentences (theoremsToAxioms refTh) localTh
  else do
    ths <- mapM (computePathTheory libEnv dg) $ sortBy
            (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1)
            $ filter (liftE $ liftOr isGlobalDef isLocalDef)
            $ innDG dg n
    flatG_sentences localTh ths

computeNodeTheory :: LibEnv -> DGraph -> Node -> Result G_theory
computeNodeTheory libEnv dg n = computeLabelTheory libEnv dg (n, labDG dg n)

computeTheory :: LibEnv -> LIB_NAME -> Node -> Result G_theory
computeTheory libEnv ln = computeNodeTheory libEnv $ lookupDGraph ln libEnv

computePathTheory :: LibEnv -> DGraph -> LEdge DGLinkLab -> Result G_theory
computePathTheory libEnv dg e@(src, _, link) = do
  th <- if liftE isLocalDef e then computeLocalNodeTheory libEnv dg src
        else computeNodeTheory libEnv dg src
  -- translate theory and turn all imported theorems into axioms
  translateG_theory (dgl_morphism link) $ theoremsToAxioms th

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2
