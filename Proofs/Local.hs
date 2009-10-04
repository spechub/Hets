{- |
Module      :  $Header$
Description :  local proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import Proofs.ComputeTheory
import Proofs.EdgeUtils
import Proofs.StatusUtils

import Logic.Grothendieck
import Logic.Prover

import Static.GTheory
import Static.DevGraph

import Common.AS_Annotation
import Common.LibName
import Common.Result
import qualified Common.OrderedMap as OMap

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Data.List

-- | local decomposition
locDecompFromList :: LibName ->  [LEdge DGLinkLab] -> LibEnv -> LibEnv
locDecompFromList ln localThmEdges libEnv=
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
    locDecompRule = DGRuleWithEdge "Local-Decomposition" ledge
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
   in Map.insert ln nextDGraph libEnv

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
      case (maybeResult $ computeLabelTheory libEnv dgraph (tgt, oldContents),
                        maybeResult $ translateG_theory morphism thSrc) of
        (Just (G_theory lidTgt _ _ sensTgt _),
              Just (G_theory lidSrc _ _ sensSrc _)) ->
          case maybeResult (coerceThSens lidTgt lidSrc "" sensTgt) of
            Nothing -> dgraph
            Just sentencesTgt ->
              -- check if all source axioms are also axioms in the target
              let goals = diffSens (OMap.filter isAxiom sensSrc) sentencesTgt
                  goals' = markAsGoal goals
                  (newTh, renms) = case dgn_theory oldContents of
                    G_theory lid sig ind sens ind' ->
                      case coerceThSens lidSrc lid "" goals' of
                        Nothing -> (G_theory lid sig ind sens ind', [])
                        Just goals'' ->
                          let (newSens, rnms) = joinSensAux sens goals''
                          in (G_theory lid sig ind newSens startThId, rnms)
                  newContents = oldContents { dgn_theory = newTh }
                  locInferRule = DGRuleLocalInference renms
                  newLab = edgeLab
                    { dgl_type = setProof (Proven locInferRule emptyProofBasis)
                        $ dgl_type edgeLab
                    , dgl_origin = DGLinkProof }
                  newEdge = (src, tgt, newLab)
                  newGraph = changesDGH dgraph
                     $ (if OMap.null goals then [] else
                         [SetNodeLab oldContents (tgt, newContents)])
                         ++ [DeleteEdge ledge, InsertEdge newEdge]
              in groupHistory dgraph locInferRule newGraph
        _ -> dgraph
    _ -> dgraph
