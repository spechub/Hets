{- |
Module      :  $Header$
Description :  compute the normal forms of all nodes in development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute normal forms
-}

module Proofs.NormalForm
    ( normalFormLibEnv
    ) where

import Logic.Logic

import Static.DevGraph
import Static.WACocone

import Proofs.EdgeUtils
import Proofs.ComputeColimit

import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.List (nub)
import Control.Monad

normalFormRule :: DGRule
normalFormRule = DGRule "NormalForm"

normalFormLibEnv :: LibEnv -> Result LibEnv
normalFormLibEnv libEnv = foldM (\ le ln -> do
  let dg = lookupDGraph ln le
  newDg <- normalFormDG le dg
  return $ Map.insert ln
    (groupHistory dg normalFormRule newDg) le)
  libEnv $ getTopsortedLibs libEnv

normalFormDG :: LibEnv -> DGraph -> Result DGraph
normalFormDG libEnv dgraph = foldM (\ dg (node, nodelab) ->
  if labelHasHiding nodelab then case dgn_nf nodelab of
    Just _ -> return dg -- already computed
    Nothing -> if isDGRef nodelab then do
        -- the normal form of the node
        -- is a reference to the normal form of the node it references
        -- careful: here not refNf, but a new Node which references refN
       let refLib = dgn_libname nodelab
           refNode = dgn_node nodelab
           refGraph' = lookupDGraph refLib libEnv
           refLabel = labDG refGraph' refNode
       case dgn_nf refLabel of
         Nothing -> warning dg
           (getDGNodeName refLabel ++ " (node " ++ show refNode
            ++ ") from '" ++ show (getLIB_ID refLib)
            ++ "' without normal form") nullRange
         Just refNf -> do
           let refNodelab = labDG refGraph' refNf
               -- the label of the normal form ^
               nfNode = getNewNodeDG dg
               -- the new reference node in the old graph ^
               tt = getName $ dgn_name nodelab
               nfName = mkSimpleId $ "NormalForm" ++ show tt ++ show node
               refLab = refNodelab {
                   dgn_name = NodeName nfName (show nfName) 0,
                   dgn_nf = Just nfNode,
                   dgn_sigma = Just $ ide $ dgn_sign refNodelab,
                   nodeInfo = newRefInfo refLib refNf,
                   dgn_lock = Nothing
                 }
               newLab = nodelab{
                   dgn_nf = Just nfNode,
                   dgn_sigma = dgn_sigma $ labDG refGraph' $ dgn_node nodelab
                 }
               chLab = SetNodeLab nodelab (node, newLab)
               changes = [InsertNode (nfNode, refLab), chLab]
               newGraph = changesDGH dgraph changes
           return newGraph
      else do
        let gd = insNode (node, dgn_theory nodelab) empty
            g0 = Map.fromList [(node, node)]
            (diagram, g) = computeDiagram dg [node] (gd, g0)
            Result ds res = gWeaklyAmalgamableCocone diagram
            es = map (\ d -> if isErrorDiag d then d { diagKind = Warning }
                             else d) ds
        appendDiags es
        case res of
          Nothing -> warning dg
                ("cocone failure for " ++ getDGNodeName nodelab
                 ++ " (node " ++ shows node ")") nullRange
          Just (sign, mmap) ->
            let nfNode = getNewNodeDG dg -- new node for normal form
                NodeName tt ss _ = dgn_name nodelab
                          -- the label of the new node
                nfName = mkSimpleId $ "NormalForm" ++ show tt ++ show node
                nfLabel = (newNodeLab (NodeName nfName ss 0)
                  (DGNormalForm node) sign)
                newLab = nodelab -- the new label for node
                     { dgn_nf = Just nfNode,
                       dgn_sigma = Just $ mmap Map.! (g Map.! node)
                     }
            -- add the nf to the label of node
                chLab = SetNodeLab nodelab (node, newLab)
            -- insert the new node and add edges from the predecessors
                insNNF = InsertNode (nfNode, nfLabel)
                makeEdge src tgt m = (src, tgt, DGLink { dgl_morphism = m
                                              , dgl_type = GlobalDef
                                              , dgl_origin = DGLinkProof
                                              , dgl_id = defaultEdgeId
                                              })
                insStrMor = map (\ (x, f) -> InsertEdge $ makeEdge x nfNode f)
                  $ nub $ map (\ (x, y) -> (g Map.! x, y))
                  $ Map.toList mmap
                allChanges = chLab : insNNF : insStrMor
            in return $ changesDGH dg allChanges
  else return dg) dgraph $ topsortedNodes dgraph -- only change relevant nodes

{- | computes the diagram associated to a node N in a development graph,
   adding common origins for multiple occurences of nodes, whenever
   needed
-}
computeDiagram :: DGraph -> [Node] -> (GDiagram, Map.Map Node Node)
               -> (GDiagram, Map.Map Node Node)
  -- as described in the paper for now
computeDiagram dgraph nodeList (gd, g) =
 case nodeList of
  [] -> (gd, g)
  _ ->
   let -- defInEdges is list of pairs (n, edges of target g(n))
       defInEdges = map (\n -> (n,filter (\e@(s,t,_) -> s /= t &&
                         liftE (liftOr isGlobalDef isHidingDef) e) $
                        innDG dgraph $ g Map.! n))  nodeList
       -- TO DO: no local links, and why edges with s=t are removed
       --        add normal form nodes
       -- sources of each edge must be added as new nodes
       nodeIds = zip (newNodes (length $ concat $ map snd defInEdges) gd)
                     $ concatMap (\(n,l) -> map (\x -> (n,x)) l ) defInEdges
       newLNodes = zip (map fst nodeIds) $
                   map (\ (s,_,_) -> dgn_theory $ labDG dgraph s) $
                   concat $  map snd defInEdges
       g0 = Map.fromList $
                     map (\ (newS, (_newT, (s,_t, _))) -> (newS,s)) nodeIds
       morphEdge (n1,(n2, (_, _, el))) =
         if isHidingDef $ dgl_type el
            then (n2, n1, (x, dgl_morphism el))
            else (n1, n2, (x, dgl_morphism el))
         where EdgeId x = dgl_id el
       newLEdges = map morphEdge nodeIds
       gd' = insEdges newLEdges $ insNodes newLNodes gd
       g' = Map.union g g0
   in computeDiagram dgraph (map fst nodeIds) (gd', g')
