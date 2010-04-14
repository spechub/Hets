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
    , computeLibEnvTheories
    , computeLabelTheory
    , markHiding
    , markFree
    ) where

import Logic.Prover

import Static.GTheory
import Static.DevGraph
import Static.History

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import Data.List (sortBy)
import qualified Data.Map as Map

-- * nodes with incoming hiding definition links

nodeHasHiding :: DGraph -> Node -> Bool
nodeHasHiding dg = labelHasHiding . labDG dg

nodeHasFree :: DGraph -> Node -> Bool
nodeHasFree dg = labelHasFree . labDG dg

isFreeEdge :: DGLinkType -> Bool
-- this is duplicated because I wanted to avoid quickly a cyclic import
isFreeEdge edge = case edge of
    FreeOrCofreeDefLink Free _ -> True
    _ -> False

{- | mark all nodes if they have incoming hiding edges.
   Assume reference nodes to other libraries being properly marked already.
-}
markFree :: LibEnv -> DGraph -> DGraph
markFree le dgraph =
  foldl (\ dg (n, lbl) -> let
     ingoingEdges = innDG dg n
     defEdges = filter (liftE isDefEdge) ingoingEdges
     freeDefEdges = filter (liftE isFreeEdge ) defEdges
     in fst $ labelNodeDG (n, lbl { labelHasFree =
            if isDGRef lbl
            then nodeHasFree (lookupDGraph (dgn_libname lbl) le)
                 $ dgn_node lbl
            else not (null freeDefEdges) }) dg)
     dgraph $ topsortedNodes dgraph

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

computeLibEnvTheories :: LibEnv -> LibEnv
computeLibEnvTheories le =
    let lns = getTopsortedLibs le
        upd le' ln = let dg0 = lookupDGraph ln le
                         dg = computeDGraphTheories le' dg0
                     in Map.insert ln dg le'
    in foldl upd Map.empty lns


computeDGraphTheories :: LibEnv -> DGraph -> DGraph
computeDGraphTheories le dgraph =
  let newDg = computeDGraphTheoriesAux le dgraph
  in groupHistory dgraph (DGRule "Compute theory") newDg

computeDGraphTheoriesAux :: LibEnv -> DGraph -> DGraph
computeDGraphTheoriesAux le dgraph =
  foldl (\ dg l@(n, lbl) -> changeDGH dg $ SetNodeLab lbl
    (n,
    let gth = computeLabelTheory le dg l in
    (case gth of
      Just th@(G_theory _ _ _ sens _) ->
         if Map.null sens then markNodeConsistent "ByNoSentences"
         else (\ lb -> lb { dgn_theory = proveLocalSens th (dgn_theory lbl) })
      _ -> id) lbl { globalTheory = gth }))
     dgraph $ topsortedNodes dgraph

computeLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> Maybe G_theory
computeLabelTheory le dg (n, lbl) = let localTh = dgn_theory lbl in
    fmap reduceTheory . maybeResult $ if isDGRef lbl then do
        let refNode = dgn_node lbl
            dg' = lookupDGraph (dgn_libname lbl) le
            newLab = labDG dg' refNode
        refTh <- getGlobalTheory newLab
        joinG_sentences refTh localTh
    else do
      ths <- mapM (\ (s, _, l) -> do
         th <- let sl = labDG dg s in if isLocalDef $ dgl_type l then
                   return $ dgn_theory sl
               else getGlobalTheory sl
         -- translate theory and turn all imported theorems into axioms
         translateG_theory (dgl_morphism l) $ theoremsToAxioms th)
         $ sortBy
            (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1)
            $ filter (liftE $ liftOr isGlobalDef isLocalDef)
            $ innDG dg n
      flatG_sentences localTh ths

reduceTheory :: G_theory -> G_theory
reduceTheory (G_theory lid sig ind sens _) =
  G_theory lid sig ind (reduceSens sens) startThId
