{- |
Module      :  
Copyright   :  (c) Cui Jian, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

theorem hide shift proof in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.
-}



module Proofs.SimpleTheoremHideShift (theoremHideShift) where

import Static.DevGraph
import Syntax.AS_Library
import Proofs.EdgeUtils
import Static.DGToSpec
import Proofs.StatusUtils

import Data.Graph.Inductive.Graph

import Debug.Trace


-- ----------------------------------------------
-- simplified theorem hide shift
-- ----------------------------------------------

theoremHideShift :: LIB_NAME -> LibEnv -> LibEnv
--theoremHideShift ln proofStatus = trace (show "haha") proofStatus
theoremHideShift ln proofStatus = 
				let dgraph = lookupDGraph ln proofStatus
				    hidingDefEdges = filter isHidingDef $ labEdges dgraph
				    (newDGraph, newHistory) = trace (show hidingDefEdges) $ theoremHideShiftFromList dgraph hidingDefEdges ([], [])
				in
				trace (show newDGraph) $ mkResultProofStatus ln proofStatus newDGraph newHistory

theoremHideShiftFromList :: DGraph -> [LEdge DGLinkLab] -> ([DGRule], [DGChange]) -> (DGraph, ([DGRule], [DGChange]))
theoremHideShiftFromList dgraph [] history = (dgraph, history)
theoremHideShiftFromList dgraph (e:hidingDefEdges) history = 
    theoremHideShiftFromList newDGraph hidingDefEdges newHistory
    where
    (newDGraph, newChanges) = theoremHideShiftWithOneHidingDefEdge dgraph e
    newHistory = if(null newChanges) then (TheoremHideShift:(fst history), newChanges++(snd history))
				       else history

theoremHideShiftWithOneHidingDefEdge :: DGraph -> LEdge DGLinkLab -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdge dgraph e =
    let
    n = getTargetNode e
    globalUnprovenEdges = getInComingGlobalUnprovenEdges dgraph n
    in
    trace (show globalUnprovenEdges) $ theoremHideShiftWithOneHidingDefEdgeAux dgraph e globalUnprovenEdges []
    --trace (show globalUnprovenEdges) $ (dgraph, []) 

getInComingGlobalUnprovenEdges :: DGraph -> Node -> [LEdge DGLinkLab]
getInComingGlobalUnprovenEdges dgraph n = filter (\e -> (getTargetNode e == n) && (isUnprovenGlobalThm e)) $ labEdges dgraph

theoremHideShiftWithOneHidingDefEdgeAux :: DGraph -> LEdge DGLinkLab -> [LEdge DGLinkLab] -> [DGChange] -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdgeAux dgraph _ [] changes = (dgraph, changes)
theoremHideShiftWithOneHidingDefEdgeAux dgraph e (x@(s,t,lab):xs) changes = 
    trace (show "haha") $ theoremHideShiftWithOneHidingDefEdgeAux newDGraph e xs newChanges
    where
    (GlobalThm _ conservativity conservStatus) = (dgl_type lab)
    proofBasis = []
    provenEdge = (s,
                  t,
                  DGLink {dgl_morphism = dgl_morphism lab,
                          dgl_type =
                            (GlobalThm (Proven TheoremHideShift proofBasis)
                             conservativity conservStatus),
                          dgl_origin = DGProof}
                  )
    newDGraph = insEdge provenEdge $ deLLEdge x dgraph
    newChanges = (DeleteEdge x):((InsertEdge provenEdge):changes)











