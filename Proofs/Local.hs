{- |
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

local proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-

Order of rule application: try to use local links induced by %implies
for subsumption proofs (such that the %implied formulas need not be
re-proved)

-}

module Proofs.Local (localInference, locDecomp) where

import Proofs.EdgeUtils
import Proofs.StatusUtils
import Logic.Grothendieck
import Logic.Prover
import Static.DevGraph
import Static.DGToSpec
import Syntax.AS_Library
import Common.Result
import Common.Utils
import qualified Common.Lib.Map as Map
import qualified Common.OrderedMap as OMap
import Data.Graph.Inductive.Graph
import Data.Maybe

-- --------------------
-- local decomposition
-- --------------------

{- a merge of the rules local subsumption, local decomposition I and
   local decomposition II -}
-- applies this merge of rules to all unproven localThm edges if possible
locDecomp :: LIB_NAME -> LibEnv -> LibEnv
locDecomp ln libEnv =
  let dgraph = lookupDGraph ln libEnv
      localThmEdges = filter isUnprovenLocalThm (labEdges dgraph)
      (nextDGraph, nextHistoryElem) =
          locDecompAux libEnv ln dgraph ([],[]) localThmEdges
  in mkResultProofStatus ln libEnv nextDGraph nextHistoryElem

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> LIB_NAME -> DGraph -> ([DGRule],[DGChange])
             -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
locDecompAux _ _ dgraph historyElement [] = (dgraph, historyElement)
locDecompAux libEnv ln dgraph (rules,changes)
                 (ledge@(src, tgt, edgeLab) : list) =
  if (null proofBasis && not (isIdentityEdge ledge libEnv dgraph))
     then
       locDecompAux libEnv ln dgraph (rules, changes) list
     else
       if isDuplicate newEdge dgraph changes
          then locDecompAux libEnv ln auxGraph
                 (newRules, DeleteEdge ledge : changes) list
       else locDecompAux libEnv ln newGraph (newRules,newChanges) list
  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    th = computeLocalTheory libEnv ln src
    pathsWithoutEdgeItself = filter (notElem ledge) allPaths
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
    proofBasis = selectProofBasis dgraph ledge filteredPaths
    auxGraph = delLEdge ledge dgraph
    LocalThm _ conservativity conservStatus = dgl_type edgeLab
    newEdge = (src,
               tgt,
               DGLink {dgl_morphism = morphism,
                       dgl_type =
                         (LocalThm (Proven (LocDecomp ledge) proofBasis)
                          conservativity conservStatus),
                       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules =  LocDecomp ledge : rules
    newChanges = DeleteEdge ledge : InsertEdge newEdge : changes

{- | removes all paths from the given list of paths whose morphism does
not translate the given sentence list to the same resulting sentence
list as the given morphism. -}
filterByTranslation :: Maybe G_theory -> GMorphism -> [[LEdge DGLinkLab]]
                    -> [[LEdge DGLinkLab]]
filterByTranslation maybeTh morphism paths =
  case maybeTh of
    Just th -> filter (isSameTranslation th morphism) paths
    Nothing -> []
--     isSameTranslation th morphism (calculateMorphismOfPath path)]

{- | checks if the given morphism and the morphism of the given path
translate the given sentence list to the same resulting sentence list. -}
isSameTranslation :: G_theory -> GMorphism -> [LEdge DGLinkLab] -> Bool
isSameTranslation th morphism path =
  case calculateMorphismOfPath path of
      Just morphismOfPath ->
         maybeResult (translateG_theory morphism th) ==
                     maybeResult (translateG_theory morphismOfPath th)
      Nothing -> False

-- ----------------------------------------------
-- local inference
-- ----------------------------------------------

-- applies local subsumption to all unproven local theorem edges
localInference :: LIB_NAME -> LibEnv -> LibEnv
localInference ln libEnv =
  let dgraph = lookupDGraph ln libEnv
      localThmEdges = filter isUnprovenLocalThm (labEdges dgraph)
      (nextDGraph, nextHistoryElem) =
          localInferenceAux libEnv ln dgraph ([],[]) localThmEdges
  in mkResultProofStatus ln libEnv nextDGraph nextHistoryElem

-- auxiliary method for localInference
localInferenceAux :: LibEnv -> LIB_NAME -> DGraph -> ([DGRule],[DGChange])
                  -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
localInferenceAux _ _ dgraph historyElement [] = (dgraph, historyElement)
localInferenceAux libEnv ln dgraph (rules, changes)
                      (ledge@(src,tgt,edgeLab) : list) =
  case maybeThSrc of
    Just thSrc ->
      case (maybeResult (computeTheory libEnv ln tgt),
                        maybeResult (translateG_theory morphism thSrc)) of
        (Just (G_theory lidTgt _ sensTgt), Just (G_theory lidSrc _ sensSrc)) ->
          case maybeResult (coerceThSens lidTgt lidSrc "" sensTgt) of
            Nothing -> localInferenceAux libEnv ln dgraph (rules,changes) list
            Just sentencesTgt ->
              -- check if all source axioms are also axioms in the target
              let goals = OMap.filter isAxiom sensSrc
                           `diffSens` sentencesTgt
                  goals' = markAsGoal goals
                  newTh = case (dgn_theory oldContents) of
                          G_theory lid sig sens ->
                           case coerceThSens lidSrc lid "" goals' of
                             Nothing -> G_theory lid sig sens
                             Just goals'' ->
                                 G_theory lid sig (sens `joinSens` goals'')
             in if OMap.null goals
                then
                 let newEdge = (src, tgt, newLab)
                     newGraph = insEdge newEdge auxGraph
                     newChanges = changes ++
                                  [DeleteEdge ledge, InsertEdge newEdge]
                 in localInferenceAux libEnv ln newGraph
                        (newRules,newChanges) list
                else
                 let newNodeLab = oldContents{dgn_theory = newTh}
                     (newGraph,changes') =
                           adjustNode auxGraph oldNode newNodeLab
                     newEdge = (src, tgt, newLab)
                     newGraph' = insEdge newEdge newGraph
                     newLibEnv = Map.adjust adjMap ln libEnv
                     adjMap ge = ge { devGraph = newGraph'}
                     newChanges = changes ++ DeleteEdge ledge :
                                  changes' ++ [InsertEdge newEdge]
                 in localInferenceAux newLibEnv ln newGraph'
                        (newRules,newChanges) list
        _ -> localInferenceAux libEnv ln dgraph (rules,changes) list
    _ -> localInferenceAux libEnv ln dgraph (rules,changes) list
  where
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalTheory libEnv ln src
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newLab = DGLink {dgl_morphism = morphism,
                       dgl_type =
                         (LocalThm (Proven (LocInference ledge) [])
                          conservativity conservStatus),
                       dgl_origin = DGProof}
    newRules = LocInference ledge : rules
    oldNode = labNode' (safeContext "localInferenceAux" dgraph tgt)
    (_,oldContents) = oldNode
    replaceNode from to (src',tgt',labl) =
       (replaceNodeAux from to src', replaceNodeAux from to tgt',labl)
    replaceNodeAux from to n = if n==from then to else n
