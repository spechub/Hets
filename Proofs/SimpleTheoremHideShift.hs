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

module Proofs.SimpleTheoremHideShift(theoremHideShift) where

import Static.DevGraph
import Syntax.AS_Library
import Proofs.EdgeUtils
import Static.DGToSpec
import Proofs.StatusUtils

import Data.Graph.Inductive.Graph

-- ----------------------------------------------
-- simplified theorem hide shift
-- ----------------------------------------------

{- | to be exported function.
     firstly it gets all the hiding definition links out of DGraph and 
     passes them to theoremHideShiftFromList which does the actual processing
-}
theoremHideShift :: LIB_NAME -> LibEnv -> LibEnv
theoremHideShift ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        hidingDefEdges = filter (liftE isHidingDef) $ labEdgesDG dgraph
        (newDGraph, newHistory) =
            theoremHideShiftFromList dgraph hidingDefEdges ([], [])
    in mkResultProofStatus ln proofStatus newDGraph newHistory

{- | apply the theorem hide shift with a list of hiding definition links.
     it calls the function for one hiding edge at a time and fills the history
     if necessary.
-}
theoremHideShiftFromList :: DGraph -> [LEdge DGLinkLab] -> 
                            ([DGRule], [DGChange]) -> 
                            (DGraph, ([DGRule], [DGChange]))
theoremHideShiftFromList dgraph [] history = (dgraph, history)
theoremHideShiftFromList dgraph (e : hidingDefEdges) history =
    theoremHideShiftFromList newDGraph hidingDefEdges newHistory
    where
    (newDGraph, newChanges) = theoremHideShiftWithOneHidingDefEdge dgraph e
    newHistory = 
       if(not $ null newChanges) then 
              (TheoremHideShift:(fst history), newChanges++(snd history))
                                 else history

{- | apply the rule to one hiding definition link.
     it takes all the related global unproven edges to the given hiding edge
     and passes them together to its auxiliary function.
-}
theoremHideShiftWithOneHidingDefEdge :: DGraph -> LEdge DGLinkLab 
                                        -> (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdge dgraph e@(_, n, _) =
    let
    globalUnprovenEdges = getInComingGlobalUnprovenEdges dgraph n
    in
    theoremHideShiftWithOneHidingDefEdgeAux dgraph e globalUnprovenEdges []

{- | get all the global unproven threorem links which go into the given 
     node in the given dgraph
-}
getInComingGlobalUnprovenEdges :: DGraph -> Node -> [LEdge DGLinkLab]
getInComingGlobalUnprovenEdges dgraph n = filter ( \ (_, t, l) ->
    t == n && isUnprovenGlobalThm (dgl_type l)) $ labEdgesDG dgraph

{- | it's the main function of this simplified theorem hide shift.
     it applies the rule to a list of global unproven threorem links 
     with the related hiding definition link. It contains three steps
     fulfilling the task and is marked below. 
-}
theoremHideShiftWithOneHidingDefEdgeAux :: DGraph -> LEdge DGLinkLab -> 
                                           [LEdge DGLinkLab] -> [DGChange] -> 
                                           (DGraph, [DGChange])
theoremHideShiftWithOneHidingDefEdgeAux dgraph _ [] changes = (dgraph, changes)
theoremHideShiftWithOneHidingDefEdgeAux dgraph (hd@(hds, _, _)) 
    (x@(s, t, lbl) : xs) changes =
    theoremHideShiftWithOneHidingDefEdgeAux finalDGraph hd xs finalChanges
    where
    ---------------------------------------------------------------
    -------- to insert an unproven global theorem link ------------
    ---------------------------------------------------------------
    newMorphism = case calculateMorphismOfPath ([x,hd]) of
                       Just m -> m
                       Nothing -> error $ "Proofs.SimpleTheoremHideShift." 
                               ++ "theoremHideShiftWithOneHidingDefEdgeAux:"
                               ++ " could not compose two morphisms"
    newGlobalEdge = (s,
                     hds,
                     DGLink {dgl_morphism = newMorphism,
                          dgl_type = (GlobalThm LeftOpen
                                      None LeftOpen),
                          dgl_origin = DGProof,
                          dgl_id = defaultEdgeID}
                 )
    ((newDGraph, newChanges), proofBasis) = 
         tryToInsertEdgeAndSelectProofBasis dgraph newGlobalEdge changes []
    ---------------------------------------------------------------
    -------- to insert a proven global theorem link ---------------
    ---------------------------------------------------------------
    (GlobalThm _ conservativity conservStatus) = dgl_type lbl
    provenEdge = (
                 s,
                 t,
                 DGLink {
                        dgl_morphism = dgl_morphism lbl,
                        dgl_type = (GlobalThm (Proven 
                                               TheoremHideShift 
                                               proofBasis) 
                                    conservativity 
                                    conservStatus),
                        dgl_origin = DGProof,
                        dgl_id = dgl_id lbl
                        }
                 )
    (newDGraph2, newChanges2) = --tryToInsertEdge newDGraph provenEdge newChanges
        insertDGLEdge provenEdge newDGraph newChanges
    --------------------------------------------------------------------------------
    -------- delete the being processed unproven global theorem link ---------------
    --------------------------------------------------------------------------------
    (finalDGraph, finalChanges) = updateWithOneChange (DeleteEdge x) newDGraph2 newChanges2

{- | it tries to insert the given edge into the DGraph and selects the
     inserted edge as proof basis if possible.
-}
tryToInsertEdgeAndSelectProofBasis :: DGraph -> LEdge DGLinkLab -> 
                                      [DGChange] -> 
                                      [EdgeID] ->
                                      ((DGraph, [DGChange]), [EdgeID])
tryToInsertEdgeAndSelectProofBasis dgraph newEdge changes proofbasis =
   case (tryToGetEdge newEdge dgraph changes) of
        Just tempE -> ((dgraph, changes), ((getEdgeID tempE):proofbasis))
        Nothing -> let
                   (tempDGraph, tempChanges) = 
                       updateWithOneChange (InsertEdge newEdge) dgraph changes
                   tempPB = case (head tempChanges) of
                               (InsertEdge tempE) -> ((getEdgeID tempE):proofbasis)
                               _ -> error ("Proofs"++
                                           ".SimpleTheoremHideShift"++
                                           ".tryToInsertEdge"++
                                           "AndSelectProofBasis")
                   in
                   ((tempDGraph, tempChanges), tempPB)  











