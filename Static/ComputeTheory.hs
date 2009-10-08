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

module Static.ComputeTheory
    ( computeTheory
    , getGlobalTheory
    , theoremsToAxioms
    , computeDGraphTheories
    , computeLabelTheory
    , markHiding
    ) where

import Logic.Prover

import Static.GTheory
import Static.DevGraph

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import Data.List (sortBy)
import Control.Monad

-- * nodes with incoming hiding definition links

nodeHasHiding :: DGraph -> Node -> Bool
nodeHasHiding dg = labelHasHiding . labDG dg

{- | mark all nodes if they have incoming hiding edges.
   Assume reference nodes to other libraries being properly marked already.
-}
markHiding :: LibEnv -> DGraph -> DGraph
markHiding le dgraph =
  foldl (\ dg (n, lbl) -> let
     ingoingEdges = innDG dg n
     defEdges = filter (liftE isDefEdge) ingoingEdges
     hidingDefEdges = filter (liftE isHidingDef ) defEdges
     next = map (\ (s, _, _) ->  s) defEdges
     in fst $ labelNodeDG (n, lbl { labelHasHiding =
            if isDGRef lbl
            then nodeHasHiding (lookupDGraph (dgn_libname lbl) le)
                 $ dgn_node lbl
            else not (null hidingDefEdges) || any (nodeHasHiding dg) next }) dg)
     dgraph $ topsortedNodes dgraph

computeTheory :: LibEnv -> LibName -> Node -> Result G_theory
computeTheory libEnv ln = globalNodeTheory $ lookupDGraph ln libEnv

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2

getGlobalTheory :: DGNodeLab -> Result G_theory
getGlobalTheory = maybe (fail "no global theory") return . globalTheory

globalNodeTheory :: DGraph -> Node -> Result G_theory
globalNodeTheory dg = getGlobalTheory . labDG dg

computeDGraphTheories :: LibEnv -> DGraph -> DGraph
computeDGraphTheories le dgraph =
  foldl (\ dg l@(n, lbl) -> fst $ labelNodeDG (n, lbl
     { globalTheory = computeLabelTheory le dg l }) dg)
     dgraph $ topsortedNodes dgraph

computeLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> Maybe G_theory
computeLabelTheory le dg (n, lbl) = let localTh = dgn_theory lbl in
    maybeResult $ if isDGRef lbl then do
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
