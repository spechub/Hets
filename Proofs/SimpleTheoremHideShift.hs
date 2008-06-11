{- |
Module      :
Copyright   :  (c) Cui Jian, Till Mossakowski, Uni Bremen 2002-2006
Description :  simple version of theorem hide shift proof rule
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

simple version of theorem hide shift proof rule for development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

   it relates to the ticket 13

-}

module Proofs.SimpleTheoremHideShift
         (theoremHideShift,
          getInComingGlobalUnprovenEdges
         ) where

import Static.DevGraph
import Syntax.AS_Library
import Proofs.EdgeUtils
--import Static.DGToSpec
import Proofs.StatusUtils

import Data.Graph.Inductive.Graph
import Data.List

{- | to be exported function.
     firstly it gets all the hiding definition links out of DGraph and
     passes them to theoremHideShiftFromList which does the actual processing
-}
theoremHideShift :: LIB_NAME -> LibEnv -> LibEnv
theoremHideShift ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        hidingDefEdges = filter (liftE isHidingDef) $ labEdgesDG dgraph
        (newDGraph, newHistory) = mapAccumL
            theoremHideShiftFromList dgraph hidingDefEdges
    in mkResultProofStatus ln proofStatus newDGraph
       (concatMap fst newHistory, concatMap snd newHistory)

{- | apply the theorem hide shift with a list of hiding definition links.
     it calls the function for one hiding edge at a time and fills the history
     if necessary.
-}
theoremHideShiftFromList :: DGraph -> LEdge DGLinkLab
                         -> (DGraph, ([DGRule], [DGChange]))
theoremHideShiftFromList dgraph e = let
    (newDGraph, newChanges) = theoremHideShiftWithOneHidingDefEdge dgraph e
    in (newDGraph, ([TheoremHideShift], concat newChanges))

{- | apply the rule to one hiding definition link.
     it takes all the related global unproven edges to the given hiding edge
     and passes them together to its auxiliary function.
-}
theoremHideShiftWithOneHidingDefEdge :: DGraph -> LEdge DGLinkLab
                                     -> (DGraph, [[DGChange]])
theoremHideShiftWithOneHidingDefEdge dgraph e@(_, n, _) =
    mapAccumL (theoremHideShiftWithOneHidingDefEdgeAux e) dgraph
      $ getInComingGlobalUnprovenEdges dgraph n

{- | get all the global unproven threorem links which go into the given
     node in the given dgraph
-}
getInComingGlobalUnprovenEdges :: DGraph -> Node -> [LEdge DGLinkLab]
getInComingGlobalUnprovenEdges dgraph =
    filter (liftE isUnprovenGlobalThm) . innDG dgraph

{- | it's the main function of this simplified theorem hide shift.
     it applies the rule to a list of global unproven threorem links
     with the related hiding definition link. It contains three steps
     fulfilling the task and is marked below.
-}
theoremHideShiftWithOneHidingDefEdgeAux :: LEdge DGLinkLab -> DGraph
                                        -> LEdge DGLinkLab
                                        -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdgeAux hd@(hds, _, _) dgraph x@(s, t, lbl) =
    (finalDGraph, newChanges ++ finalChanges)
    where
    -------- to insert an unproven global theorem link ------------
    newMorphism = case calculateMorphismOfPath [x, hd] of
      Just m -> m
      Nothing -> error
       "SimpleTheoremHideShift.theoremHideShiftWithOneHidingDefEdgeAux"
    newGlobalEdge = (s, hds, DGLink
      { dgl_morphism = newMorphism
      , dgl_type = GlobalThm LeftOpen None LeftOpen
      , dgl_origin = DGLinkProof
      , dgl_id = defaultEdgeId})
    ((newDGraph, newChanges), proofbasis) =
      tryToInsertEdgeAndSelectProofBasis dgraph newGlobalEdge emptyProofBasis
    -------- to insert a proven global theorem link ---------------
    GlobalThm _ conservativity conservStatus = dgl_type lbl
    provenEdge = (s, t, lbl
      { dgl_type = GlobalThm (Proven TheoremHideShift proofbasis)
          conservativity conservStatus
      , dgl_origin = DGLinkProof })
    (finalDGraph, finalChanges) = updateWithChanges
            [DeleteEdge x, InsertEdge provenEdge] newDGraph

{- | it tries to insert the given edge into the DGraph and selects the
     inserted edge as proof basis if possible.
-}
tryToInsertEdgeAndSelectProofBasis :: DGraph -> LEdge DGLinkLab -> ProofBasis
                                   -> ((DGraph, [DGChange]), ProofBasis)
tryToInsertEdgeAndSelectProofBasis dgraph newEdge proofbasis =
    case tryToGetEdge newEdge dgraph of
      Just tempE -> ((dgraph, []), addEdgeId proofbasis $ getEdgeId tempE)
      Nothing -> let
          (tempDGraph, tempChanges) =
              updateWithOneChange (InsertEdge newEdge) dgraph
          tempPB = case tempChanges of
            [InsertEdge tempE] -> addEdgeId proofbasis $ getEdgeId tempE
            _ -> error
              "SimpleTheoremHideShift.tryToInsertEdgeAndSelectProofBasis"
          in ((tempDGraph, tempChanges), tempPB)
