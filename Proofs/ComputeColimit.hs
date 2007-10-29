{- |
Module      :  $Header$
Description :  Heterogeneous colimit of the displayed graph
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Computes the colimit and displays the graph after its insertion.
Improvements:

 - error messages when the algorithm fails to compute
 - insert edges just from a subset of nodes in the original graph
-}

module Proofs.ComputeColimit where

import Proofs.EdgeUtils
import Proofs.StatusUtils
import Static.DevGraph
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Syntax.AS_Library
import Common.Result
import Proofs.TheoremHideShift(makeDiagram)

computeColimit :: LIB_NAME -> LibEnv -> LibEnv
computeColimit ln le = let
  dgraph = lookupDGraph ln le
  (nextDGraph, nextHistoryElem) = insertColimitInGraph dgraph
 in mkResultProofStatus ln le nextDGraph nextHistoryElem

insertColimitInGraph :: DGraph -> (DGraph,([DGRule],[DGChange]))
insertColimitInGraph dgraph = let
 diag = makeDiagram dgraph (nodes $ dgBody dgraph) (labEdges $ dgBody dgraph)
 in case maybeResult $ gWeaklyAmalgamableCocone diag of
     Nothing -> (dgraph,([],[])) -- here not ok, see later
     Just (gth, morFun) -> let
       newNode = DGNodeLab{
         dgn_name = emptyNodeName,
            -- assign new name here, gn_Signature_Colimit?
         dgn_theory = gth,
         dgn_nf = Nothing,
         dgn_sigma = Nothing,
         nodeInfo = DGNode{
           node_origin = DGProof,
           node_cons = None,
           node_cons_status = LeftOpen},
           dgn_lock = error "uninitialized MVar of DGNode"}
       newNodeNr = getNewNodeDG dgraph
       edgeList = map (\n -> (n, newNodeNr,DGLink{
                    dgl_morphism = (Map.!)morFun n,
                    dgl_type = GlobalDef,
                    dgl_origin = DGProof,
                    dgl_id = []})) $
                   nodes $ dgBody dgraph
           --dgl_id field is filled when displayed
       changes  = [InsertNode (newNodeNr, newNode)] ++ map InsertEdge edgeList
       (newGraph,newChanges) = updateWithChanges changes dgraph []
       rules = [ComputeColimit]
      in (newGraph, (rules,newChanges))



