{- |
Module      :  $Header$
Description :  local proof rukes for development graphs
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

import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.TheoremHideShift

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
locDecompFromList :: LIB_NAME ->  [LEdge DGLinkLab] -> LibEnv -> LibEnv
locDecompFromList ln localThmEdges libEnv=
   let dgraph = lookupDGraph ln libEnv
       finalLocalThmEdges = filter (liftE isUnprovenLocalThm) localThmEdges
       nextDGraph = foldl (locDecompAux libEnv ln) dgraph finalLocalThmEdges
   in Map.insert ln nextDGraph libEnv

-- | local decomposition for all edges
locDecomp :: LIB_NAME -> LibEnv -> LibEnv
locDecomp ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in locDecompFromList ln localThmEdges libEnv

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> LIB_NAME -> DGraph -> LEdge DGLinkLab -> DGraph
locDecompAux libEnv ln dgraph ledge@(src, tgt, edgeLab) = let
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    th = computeLocalTheory libEnv ln src
    pathsWithoutEdgeItself = filter (noPath ledge) allPaths
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
    proofbasis = selectProofBasis dgraph ledge filteredPaths
    auxGraph = changeDGH dgraph $ DeleteEdge ledge
    LocalThm _ conservativity conservStatus = dgl_type edgeLab
    locDecompRule = DGRuleWithEdge "Local-Decomposition" ledge
    newEdge = (src, tgt, edgeLab
      { dgl_type = LocalThm (Proven locDecompRule proofbasis)
          conservativity conservStatus
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
localInferenceFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
localInferenceFromList ln localThmEdges libEnv =
   let dgraph = lookupDGraph ln libEnv
       finalLocalThmEdges = filter (liftE isUnprovenLocalThm) localThmEdges
       (newLibEnv, nextDGraph) = foldl
               (localInferenceAux ln) (libEnv, dgraph) finalLocalThmEdges
   in Map.insert ln nextDGraph newLibEnv

-- | local inference for all edges
localInference :: LIB_NAME -> LibEnv -> LibEnv
localInference ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in localInferenceFromList ln localThmEdges libEnv

-- auxiliary method for localInference
localInferenceAux :: LIB_NAME -> (LibEnv, DGraph) -> LEdge DGLinkLab
                  -> (LibEnv, DGraph)
localInferenceAux ln (libEnv, dgraph) ledge@(src, tgt, edgeLab) = let
    noChange = (libEnv, dgraph)
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalTheory libEnv ln src
    in case maybeThSrc of
    Just thSrc ->
      case (maybeResult (computeTheory libEnv ln tgt),
                        maybeResult (translateG_theory morphism thSrc)) of
        (Just (G_theory lidTgt _ _ sensTgt _),
              Just (G_theory lidSrc _ _ sensSrc _)) ->
          case maybeResult (coerceThSens lidTgt lidSrc "" sensTgt) of
            Nothing -> noChange
            Just sentencesTgt ->
              -- check if all source axioms are also axioms in the target
              let goals = OMap.filter isAxiom sensSrc
                           `diffSens` sentencesTgt
                  goals' = markAsGoal goals
                  newTh = case dgn_theory oldContents of
                          G_theory lid sig ind sens ind' ->
                           case coerceThSens lidSrc lid "" goals' of
                             Nothing -> G_theory lid sig ind sens ind'
                             Just goals'' ->
                                 G_theory lid sig ind
                                   (sens `joinSens` goals'') startThId
                  newContents = oldContents { dgn_theory = newTh }
                  LocalThm _ conservativity conservStatus = dgl_type edgeLab
                  locInferRule = DGRuleWithEdge "Local-Inference" ledge
                  newLab = edgeLab
                    { dgl_type = LocalThm (Proven locInferRule emptyProofBasis)
                        conservativity conservStatus
                    , dgl_origin = DGLinkProof }
                  newEdge = (src, tgt, newLab)
                  oldContents = labDG dgraph tgt
                  (newLibEnv, graphWithChangedTheory) =
                    if OMap.null goals then noChange
                    else let
                      dg = changeDGH dgraph
                           $ SetNodeLab oldContents (tgt, newContents)
                      in (Map.adjust (const dg) ln libEnv, dg)
                  newGraph = changesDGH graphWithChangedTheory
                        [DeleteEdge ledge, InsertEdge newEdge]
              in (newLibEnv, groupHistory dgraph locInferRule newGraph)
        _ -> noChange
    _ -> noChange
