{- |
Module      :  $Header$
Description :  compute the theory of a node
Copyright   :  (c) Christian Maeder and DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

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
    , updateLabelTheory
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
import Data.Ord

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
     next = map (\ (s, _, _) -> s) defEdges
     in fst $ labelNodeDG (n, lbl { labelHasHiding =
            if isDGRef lbl
            then nodeHasHiding (lookupDGraph (dgn_libname lbl) le)
                 $ dgn_node lbl
            else not (null hidingDefEdges) || any (nodeHasHiding dg) next }) dg)
     dgraph $ topsortedNodes dgraph

computeTheory :: LibEnv -> LibName -> Node -> Maybe G_theory
computeTheory libEnv ln = globalNodeTheory $ lookupDGraph ln libEnv

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2

getGlobalTheory :: DGNodeLab -> Result G_theory
getGlobalTheory = maybe (fail "no global theory") return . globalTheory

globalNodeTheory :: DGraph -> Node -> Maybe G_theory
globalNodeTheory dg = globalTheory . labDG dg

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

recomputeNodeLabel :: LibEnv -> DGraph -> LNode DGNodeLab -> DGNodeLab
recomputeNodeLabel le dg l@(n, lbl) =
  case computeLabelTheory le dg l of
    gTh@(Just th) ->
      let (chg, lbl1) = case globalTheory lbl of
            Nothing -> (False, lbl)
            Just oTh -> (True, lbl
              { dgn_theory = invalidateProofs oTh th $ dgn_theory lbl })
          ngTh = if chg then computeLabelTheory le dg (n, lbl1) else gTh
      in case ngTh of
        Just nth@(G_theory _ _ _ sens _) ->
          (if Map.null sens then markNodeConsistent "ByNoSentences" lbl1
           else lbl1 { dgn_theory = proveLocalSens nth (dgn_theory lbl1) })
           { globalTheory = ngTh }
        Nothing -> lbl1
    Nothing -> lbl

computeDGraphTheoriesAux :: LibEnv -> DGraph -> DGraph
computeDGraphTheoriesAux le dgraph =
  foldl (\ dg l@(n, lbl) -> changeDGH dg $ SetNodeLab lbl
    (n, recomputeNodeLabel le dg l))
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
            (flip $ comparing (\ (_, _, l) -> dgl_id l))
            $ filter (liftE $ liftOr isGlobalDef isLocalDef)
            $ innDG dg n
      flatG_sentences localTh ths

reduceTheory :: G_theory -> G_theory
reduceTheory (G_theory lid sig ind sens _) =
  G_theory lid sig ind (reduceSens sens) startThId

updateLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> G_theory -> DGraph
updateLabelTheory le dg (i, l) gth = let
    l' = l { dgn_theory = gth }
    n = (i, l' { globalTheory = computeLabelTheory le dg (i, l') })
    dg0 = changeDGH dg $ SetNodeLab l n
    dg1 = togglePending dg0 $ changedLocalTheorems dg0 n
    dg2 = togglePending dg1 $ changedPendingEdges dg1
    in groupHistory dg (DGRule "Node proof") dg2
