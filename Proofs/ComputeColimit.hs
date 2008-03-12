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
import Static.GTheory
import Static.WACocone

import Syntax.AS_Library

import Logic.Comorphism (mkIdComorphism)
import Logic.Grothendieck
import Logic.Logic

import Common.ExtSign
import Common.Result
import Common.SFKT

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph

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
     Just (gth, morFun) -> let -- a better node name, gn_Signature_Colimit?
       newNode = newInfoNodeLab emptyNodeName (newNodeInfo DGProof) gth
       newNodeNr = getNewNodeDG dgraph
       edgeList = map (\n -> (n, newNodeNr,DGLink{
                    dgl_morphism = (Map.!)morFun n,
                    dgl_type = GlobalDef,
                    dgl_origin = SeeTarget,
                    dgl_id = defaultEdgeId})) $
                   nodes $ dgBody dgraph
           --dgl_id field is filled when displayed
       changes  = [InsertNode (newNodeNr, newNode)] ++ map InsertEdge edgeList
       (newGraph,newChanges) = updateWithChanges changes dgraph []
       rules = [ComputeColimit]
      in (newGraph, (rules, reverse newChanges))

{- | creates an GDiagram with the signatures of the given nodes as nodes
   and the morphisms of the given edges as edges -}
makeDiagram :: DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagram = makeDiagramAux empty

{- | auxiliary method for makeDiagram: first translates all nodes then
   all edges, the descriptors of the nodes are kept in order to make
   retranslation easier -}
makeDiagramAux :: GDiagram -> DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagramAux diagram _ [] [] = diagram
makeDiagramAux diagram dgraph [] ((src, tgt, labl) : list) =
  makeDiagramAux (insEdge morphEdge diagram) dgraph [] list
    where morphEdge = if isHidingDef $ dgl_type labl
                      then (tgt,src,(1,dgl_morphism labl))
 --  HERE AND BELOW SHOULD BE VALUES EXTRACTED FROM dgl_id FIELD,
 --  BUT EdgeId IS A LIST OF INTS INSTEAD OF A SINGLE INT
                      else (src,tgt,(1,dgl_morphism labl))

makeDiagramAux diagram dgraph (node:list) es =
  makeDiagramAux (insNode sigNode diagram) dgraph list es
    where sigNode = (node, dgn_theory $ labDG dgraph node)

-- | weakly amalgamable cocones
gWeaklyAmalgamableCocone :: GDiagram
                         -> Result (G_theory, Map.Map Int GMorphism)
gWeaklyAmalgamableCocone diag =
 if isHomogeneousGDiagram diag then do
  case head $ labNodes diag of
   (_, G_theory lid _ _ _ _) -> do
    graph <- homogeniseGDiagram lid diag
    (sig, mor) <- signature_colimit lid graph
                  -- until the amalgamability check is fixed
    let gth = noSensGTheory lid (mkExtSign sig) startSigId
        cid = mkIdComorphism lid (top_sublogic lid)
        morFun = Map.fromList $
         map (\(n, s)->(n, GMorphism cid (mkExtSign s) startSigId
                             (mor Map.! n) startMorId)) $
         labNodes graph
    return (gth, morFun)
 else if not $ isConnected diag then fail "Graph is not connected"
      else if not $ isAcyclic $ removeIdentities diag then
             -- TO DO: instead of acyclic, test whether the diagram is thin
           fail "Graph is not acyclic" else do
             let funDesc = initDescList diag
             graph <- observe $ hetWeakAmalgCocone diag funDesc
               -- TO DO: modify this function so it would return
               -- all possible answers and offer them as choices to the user
             buildStrMorphisms diag graph
