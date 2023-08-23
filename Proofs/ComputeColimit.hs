{- |
Module      :  ./Proofs/ComputeColimit.hs
Description :  Heterogeneous colimit of the displayed graph
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Computes the colimit and displays the graph after its insertion.
Improvements:

 - error messages when the algorithm fails to compute
 - insert edges just from a subset of nodes in the original graph
-}

module Proofs.ComputeColimit where

import Static.ComputeTheory
import Static.DevGraph
import Static.DgUtils
import Static.GTheory
import Static.History
import Static.WACocone

import Logic.Comorphism (mkIdComorphism)
import Logic.Grothendieck
import Logic.Logic

import Common.ExtSign
import Common.LibName
import Common.Result
import Common.SFKT
import Common.Id
import Common.IRI
import Common.Utils (nubOrd)
import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph

-- | computes the colimit of one development graph in a LibEnv
computeColimit :: LibName -> LibEnv -> Result LibEnv
computeColimit ln le = do
  let dgraph = lookupDGraph ln le
  (_, nextDGraph) <- insertColimitInGraph le ln dgraph (nodesDG dgraph)
                                         (labEdgesDG dgraph) $
                                         makeName $
                                         simpleIdToIRI $ genToken "Colimit"
  return $ Map.insert ln nextDGraph le

insertColimitInGraph :: LibEnv -> LibName -> DGraph -> [Node] -> [LEdge DGLinkLab] -> NodeName
                     -> Result (NodeSig, DGraph)
insertColimitInGraph le ln dgraph cNodes cEdges colimName = do
  let diag = makeDiagram dgraph cNodes cEdges
  (gth, morFun) <- gWeaklyAmalgamableCocone diag
  let
      newNode = newInfoNodeLab colimName
                               (newNodeInfo DGProof) gth
      newNodeNr = getNewNodeDG dgraph
      edgeList = map (\ n -> (n, newNodeNr, globDefLink
                      (morFun Map.! n) SeeTarget))
                 cNodes
      changes = InsertNode (newNodeNr, newNode) : map InsertEdge edgeList
      newDg = changesDGH dgraph changes
      newGraph = changeDGH newDg $ SetNodeLab newNode
        (newNodeNr, newNode
        { globalTheory = computeLabelTheory le ln newDg (newNodeNr, newNode) })
      nsig = NodeSig newNodeNr (signOf gth)
      dg = groupHistory dgraph (DGRule "Compute-Colimit") newGraph
  return (nsig, dg)

{- | creates an GDiagram with the signatures of the given nodes as nodes
   and the morphisms of the given edges as edges -}
makeDiagram :: DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagram dg nl = makeDiagramAux empty dg (nubOrd nl)

{- | auxiliary method for makeDiagram: first translates all nodes then
   all edges, the descriptors of the nodes are kept in order to make
   retranslation easier -}
makeDiagramAux :: GDiagram -> DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagramAux diagram _ [] [] = diagram
makeDiagramAux diagram dgraph [] ((src, tgt, labl) : list) =
  makeDiagramAux (insEdge morphEdge diagram) dgraph [] list
    where EdgeId x = dgl_id labl
          morphEdge = if isHidingDef $ dgl_type labl
                      then (tgt, src, (x, dgl_morphism labl))
                      else (src, tgt, (x, dgl_morphism labl))

makeDiagramAux diagram dgraph (node : list) es =
  makeDiagramAux (insNode sigNode diagram) dgraph list es
    where sigNode = (node, dgn_theory $ labDG dgraph node)

-- | weakly amalgamable cocones
gWeaklyAmalgamableCocone :: GDiagram
                         -> Result (G_theory, Map.Map Int GMorphism)
gWeaklyAmalgamableCocone diag
 | isHomogeneousGDiagram diag = case head $ labNodes diag of
   (_, G_theory lid _ _ _ _ _) -> do
    graph <- homogeniseGDiagram lid diag
    (sig, mor) <- weakly_amalgamable_colimit lid graph
    let esign = (mkExtSign sig) {nonImportedSymbols = foldl Set.union Set.empty $ sym_of lid sig}
        gth = noSensGTheory lid esign startSigId
        cid = mkIdComorphism lid (top_sublogic lid)
        morFun = Map.fromList $
         map (\ (n, s) -> (n, GMorphism cid (mkExtSign s) startSigId
                             (mor Map.! n) startMorId)) $
         labNodes graph
    return (gth, morFun)
 | not $ isConnected diag = Fail.fail "Graph is not connected"
 | not $ isThin $ removeIdentities diag = Fail.fail "Graph is not thin"
 | otherwise = do
   let funDesc = initDescList diag
   -- graph <- observe $ hetWeakAmalgCocone diag funDesc
   allGraphs <- runM Nothing $ hetWeakAmalgCocone diag funDesc
   case allGraphs of
    [] -> Fail.fail "could not compute cocone"
    _ -> do
     let graph = head allGraphs
     {- TO DO: modify this function so it would return
     all possible answers and offer them as choices to the user -}
     buildStrMorphisms diag graph
