{- |
Module      :  ./Proofs/Local.hs
Description :  local proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

local proof rules for development graphs
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-

Order of rule application: try to use local links induced by %implies
for subsumption proofs (such that the %implied formulas need not be
re-proved)

-}

module Proofs.Local
    ( localInference
    , locDecomp
    , locDecompFromList
    , localInferenceFromList
    ) where

import Proofs.EdgeUtils
import Proofs.StatusUtils

import Logic.Grothendieck
import Logic.Prover

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.History
import Static.ComputeTheory

import Common.AS_Annotation
import Common.LibName
import Common.Result
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import Data.Maybe

-- | local decomposition
locDecompFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
locDecompFromList ln localThmEdges libEnv =
   let dgraph = lookupDGraph ln libEnv
       finalLocalThmEdges = filter (liftE isUnprovenLocalThm) localThmEdges
       nextDGraph = foldl (locDecompAux libEnv ln) dgraph finalLocalThmEdges
   in Map.insert ln nextDGraph libEnv

-- | local decomposition for all edges
locDecomp :: LibName -> LibEnv -> LibEnv
locDecomp ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in locDecompFromList ln localThmEdges libEnv

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> LibName -> DGraph -> LEdge DGLinkLab -> DGraph
locDecompAux libEnv ln dgraph ledge@(src, tgt, edgeLab) = let
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    th = computeLocalTheory libEnv ln src
    pathsWithoutEdgeItself = filter (noPath ledge) allPaths
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
    proofbasis = selectProofBasis dgraph ledge filteredPaths
    auxGraph = changeDGH dgraph $ DeleteEdge ledge
    locDecompRule = DGRuleWithEdge "Local-Decomposition" $ getEdgeId ledge
    newEdge = (src, tgt, edgeLab
      { dgl_type = setProof (Proven locDecompRule proofbasis)
          $ dgl_type edgeLab
      , dgl_origin = DGLinkProof })
    newGraph = insertDGLEdge newEdge auxGraph
    in if not (isIdentityEdge ledge libEnv dgraph) && nullProofBasis proofbasis
     then dgraph else
     groupHistory dgraph locDecompRule newGraph


{- | removes all paths from the given list of paths whose morphism does
not translate the given sentence list to the same resulting sentence
list as the given morphism. -}
filterByTranslation :: Maybe G_theory -> GMorphism -> [[LEdge DGLinkLab]]
                    -> [[LEdge DGLinkLab]]
filterByTranslation maybeTh morphism paths =
  case maybeTh of
    Just th -> filter (isSameTranslation th morphism) paths
    Nothing -> []

{- | checks if the given morphism and the morphism of the given path
translate the given sentence list to the same resulting sentence list. -}
isSameTranslation :: G_theory -> GMorphism -> [LEdge DGLinkLab] -> Bool
isSameTranslation th morphism path =
  case calculateMorphismOfPath path of
      Just morphismOfPath ->
         maybeResult (translateG_theory morphism th) ==
                     maybeResult (translateG_theory morphismOfPath th)
      Nothing -> False

-- | local inference
localInferenceFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
localInferenceFromList ln localThmEdges libEnv =
    localInferenceFromAux ln libEnv (lookupDGraph ln libEnv) localThmEdges

localInferenceFromAux :: LibName -> LibEnv -> DGraph -> [LEdge DGLinkLab]
  -> LibEnv
localInferenceFromAux ln libEnv dgraph localThmEdges =
   let finalLocalThmEdges = filter (liftE isUnprovenLocalThm) localThmEdges
       nextDGraph = foldl (localInferenceAux libEnv) dgraph finalLocalThmEdges
   in Map.insert ln (computeDGraphTheories libEnv ln nextDGraph) libEnv

-- | local inference for all edges
localInference :: LibName -> LibEnv -> LibEnv
localInference ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in localInferenceFromAux ln libEnv dgraph localThmEdges

-- auxiliary method for localInference
localInferenceAux :: LibEnv -> DGraph -> LEdge DGLinkLab -> DGraph
localInferenceAux libEnv dgraph ledge@(src, tgt, edgeLab) = let
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalNodeTheory libEnv dgraph src
    oldContents = labDG dgraph tgt
    in case maybeThSrc of
    Just thSrc ->
      case (computeLocalNodeTheory libEnv dgraph tgt,
                        maybeResult $ translateG_theory morphism thSrc) of
        (Just th@(G_theory lidTgt syn sig ind sensTgt _),
              Just (G_theory lidSrc _ _ _ sentensSrc _)) ->
          case maybeResult (coerceThSens lidSrc lidTgt "" sentensSrc) of
            Nothing -> dgraph
            Just sensSrc ->
              -- check if all source axioms are also axioms in the target
              let goals = OMap.filter isAxiom sensSrc
                  goals' = markAsGoal goals
                  noGoals = Map.null goals'
                  (newSens, renms) = joinSensAux sensTgt goals'
                  provenSens = proveSens lidTgt newSens
                  pendingGoals =
                    any (not . isProvenSenStatus
                         . fromMaybe (error "localInferenceAux")
                         . flip OMap.lookup provenSens)
                        $ map snd renms
                  newTh = if noGoals then th else
                    G_theory lidTgt syn sig ind provenSens startThId
                  newContents = oldContents { dgn_theory = newTh }
                  locInferRule = DGRuleLocalInference renms
                  newLab = edgeLab
                    { dgl_type = setProof (Proven locInferRule emptyProofBasis)
                        $ dgl_type edgeLab
                    , dgl_origin = DGLinkProof
                    , dglPending = pendingGoals }
                  newEdge = (src, tgt, newLab)
                  newGraph0 = changesDGH dgraph
                     $ (if noGoals then [] else
                         [SetNodeLab oldContents (tgt, newContents)])
                         ++ [DeleteEdge ledge, InsertEdge newEdge]
                  newGraph =
                    togglePending newGraph0 $ changedPendingEdges newGraph0
              in groupHistory dgraph locInferRule newGraph
        _ -> dgraph
    _ -> dgraph
