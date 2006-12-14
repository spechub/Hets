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
--import Proofs.EdgeUtils

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
				    (newDGraph, newHistory) = theoremHideShiftFromList dgraph hidingDefEdges ([], []) 
				    --trace (show hidingDefEdges) $ 				   
				in
				--trace (show newDGraph) $ 
				mkResultProofStatus ln proofStatus newDGraph newHistory

theoremHideShiftFromList :: DGraph -> [LEdge DGLinkLab] -> ([DGRule], [DGChange]) -> (DGraph, ([DGRule], [DGChange]))
theoremHideShiftFromList dgraph [] history = (dgraph, history)
theoremHideShiftFromList dgraph (e:hidingDefEdges) history = 
    theoremHideShiftFromList newDGraph hidingDefEdges newHistory
    where
    (newDGraph, newChanges) = trace ("the edge: "++show e++"\n") $ theoremHideShiftWithOneHidingDefEdge dgraph e
    newHistory = if(not $ null newChanges) then (TheoremHideShift:(fst history), newChanges++(snd history))
				       else history

theoremHideShiftWithOneHidingDefEdge :: DGraph -> LEdge DGLinkLab -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdge dgraph e =
    let
    n = getTargetNode e
    globalUnprovenEdges = getInComingGlobalUnprovenEdges dgraph n
    in
    --trace (show globalUnprovenEdges) $ 
    theoremHideShiftWithOneHidingDefEdgeAux dgraph e globalUnprovenEdges []
    --trace (show globalUnprovenEdges) $ (dgraph, []) 

getInComingGlobalUnprovenEdges :: DGraph -> Node -> [LEdge DGLinkLab]
getInComingGlobalUnprovenEdges dgraph n = filter (\e -> (getTargetNode e == n) && (isUnprovenGlobalThm e)) $ labEdges dgraph

theoremHideShiftWithOneHidingDefEdgeAux :: DGraph -> LEdge DGLinkLab -> [LEdge DGLinkLab] -> [DGChange] -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdgeAux dgraph _ [] changes = 
    if(null changes) then (dgraph, changes)
		     else (dgraph, changes)
theoremHideShiftWithOneHidingDefEdgeAux dgraph (hd@(hds, _, _)) (x@(s,t,lab):xs) changes = 
    --trace (show "haha") $ 
    theoremHideShiftWithOneHidingDefEdgeAux finalDGraph hd xs finalChanges
    where
    ---------------------------------------------------------------
    -------- to insert an unproven global theorem link ------------
    ---------------------------------------------------------------
    newMorphism = case calculateMorphismOfPath (x:[hd]) of
		       Just m -> m
		       Nothing -> error "Proofs.SimpleTheoremHideShift.theoremHideShiftWithOneHidingDefEdgeAux: could not compose two morphisms"
    newGlobalEdge = (s,
		     hds,
		     DGLink {dgl_morphism = newMorphism,
                          dgl_type = (GlobalThm LeftOpen
                                      None LeftOpen),
                          dgl_origin = DGProof}
                 )
    (newDGraph, newChanges) = tryToInsertEdge dgraph newGlobalEdge changes
    ---------------------------------------------------------------
    -------- to insert a proven global theorem link ---------------
    ---------------------------------------------------------------
    (GlobalThm _ conservativity conservStatus) = dgl_type lab
    proofBasis = [newGlobalEdge] --selectProof newDGraph x [[]]
    provenEdge = (
		 s,
		 t,
		 DGLink {
			dgl_morphism = dgl_morphism lab,
			-- ? TheoremHideShift should be with an edge or not?
			dgl_type = (GlobalThm (Proven TheoremHideShift proofBasis) conservativity conservStatus),
			dgl_origin = DGProof
			}
		 )
    (newDGraph2, newChanges2) = tryToInsertEdge newDGraph provenEdge newChanges
    --------------------------------------------------------------------------------
    -------- delete the being processed unproven global theorem link ---------------
    --------------------------------------------------------------------------------
    (finalDGraph, finalChanges) = (deLLEdge x newDGraph2, (DeleteEdge x):newChanges2)

tryToInsertEdge :: DGraph -> LEdge DGLinkLab -> [DGChange] -> (DGraph, [DGChange])
tryToInsertEdge dgraph newEdge changes = 
	case isDuplicate newEdge dgraph changes of
	     True -> (dgraph, changes)
	     False -> ((insEdge newEdge dgraph), (InsertEdge newEdge):changes) 











