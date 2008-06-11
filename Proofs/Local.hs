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
import Logic.Grothendieck
import Logic.Prover
import Static.GTheory
import Static.DevGraph
import Syntax.AS_Library
import Common.Result
import Common.AS_Annotation
import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap
import Data.Graph.Inductive.Graph
import Data.List

import Proofs.TheoremHideShift

-- | local decomposition
locDecompFromList :: LIB_NAME ->  [LEdge DGLinkLab] -> LibEnv -> LibEnv
locDecompFromList ln localThmEdges libEnv=
   let dgraph = lookupDGraph ln libEnv
       finalLocalThmEdges = filter (liftE isUnprovenLocalThm) localThmEdges
       (nextDGraph, nextHistoryElems) =
           mapAccumL (locDecompAux libEnv ln) dgraph finalLocalThmEdges
   in mkResultProofStatus ln libEnv nextDGraph
         (concatMap fst nextHistoryElems, concatMap snd nextHistoryElems)

-- | local decomposition for all edges
locDecomp :: LIB_NAME -> LibEnv -> LibEnv
locDecomp ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in locDecompFromList ln localThmEdges libEnv

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> LIB_NAME -> DGraph -> LEdge DGLinkLab
             -> (DGraph, ([DGRule], [DGChange]))
locDecompAux libEnv ln dgraph ledge@(src, tgt, edgeLab) =
  if not (isIdentityEdge ledge libEnv dgraph) && nullProofBasis proofbasis
     then (dgraph, emptyHistory)
     else (newGraph, (newRules, delChange ++ insChange))
  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    th = computeLocalTheory libEnv ln src
    pathsWithoutEdgeItself = filter (noPath ledge) allPaths
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
    proofbasis = selectProofBasis dgraph ledge filteredPaths
    (auxGraph, delChange) =
        updateWithOneChange (DeleteEdge ledge) dgraph
    LocalThm _ conservativity conservStatus = dgl_type edgeLab
    newEdge = (src, tgt, edgeLab
      { dgl_type = LocalThm (Proven (LocDecomp ledge) proofbasis)
                          conservativity conservStatus
      , dgl_origin = DGLinkProof })
    (newGraph, insChange) =
        insertDGLEdge newEdge auxGraph
    newRules = [LocDecomp ledge]

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
       ((newLibEnv, nextDGraph), nextHistoryElems) = mapAccumL
               (localInferenceAux ln) (libEnv, dgraph) finalLocalThmEdges
   in mkResultProofStatus ln newLibEnv nextDGraph
               (concatMap fst nextHistoryElems, concatMap snd nextHistoryElems)

-- | local inference for all edges
localInference :: LIB_NAME -> LibEnv -> LibEnv
localInference ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        localThmEdges = labEdgesDG dgraph
    in localInferenceFromList ln localThmEdges libEnv

-- auxiliary method for localInference
localInferenceAux :: LIB_NAME -> (LibEnv, DGraph) -> LEdge DGLinkLab
                  -> ((LibEnv, DGraph), ([DGRule], [DGChange]))
localInferenceAux ln (libEnv, dgraph) ledge@(src, tgt, edgeLab) = let
    noChange = ((libEnv, dgraph), emptyHistory)
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalTheory libEnv ln src
    in case maybeThSrc of
    Just thSrc ->
      case (maybeResult (computeTheory libEnv ln tgt),
                        maybeResult (translateG_theory morphism thSrc)) of
        (Just (libEnv', G_theory lidTgt _ _ sensTgt _),
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
                  newLab = edgeLab
                    { dgl_type = LocalThm
                        (Proven (LocInference ledge) emptyProofBasis)
                        conservativity conservStatus
                    , dgl_origin = DGLinkProof }
                  newEdge = (src, tgt, newLab)
                  newRules = [LocInference ledge]
                  oldContents = labDG dgraph tgt
                  (newLibEnv, (graphWithChangedTheory, change)) =
                    if OMap.null goals then (libEnv', (dgraph, []))
                    else let
                      p@(dg, _) = updateWithOneChange
                                  (SetNodeLab oldContents (tgt, newContents))
                                  dgraph
                      in (Map.adjust (const dg) ln libEnv', p)
                  (newGraph, newChanges) = updateWithChanges
                        [DeleteEdge ledge, InsertEdge newEdge]
                        graphWithChangedTheory
              in ((newLibEnv, newGraph), (newRules, change ++ newChanges))
        _ -> noChange
    _ -> noChange
