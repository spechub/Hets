{- |
Module      :  $Header$
Description :  compute the normal forms of all nodes in development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute normal forms
-}

module Proofs.NormalForm
    ( normalFormLibEnv
    , normalForm
    , normalFormRule
    ) where

import Logic.Logic
import Logic.Grothendieck

import Static.ComputeTheory
import Static.GTheory
import Static.DgUtils
import Static.DevGraph
import Static.History
import Static.WACocone

import Proofs.ComputeColimit

import Common.Consistency
import Common.Id
import Common.LibName
import Common.Result
import Common.Lib.Graph
import Common.Utils (nubOrd)

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Control.Monad

normalFormRule :: DGRule
normalFormRule = DGRule "NormalForm"

-- | compute normal form for a library and imported libs
normalForm :: LibName -> LibEnv -> Result LibEnv
normalForm ln le = normalFormLNS (dependentLibs ln le) le

-- | compute norm form for all libraries
normalFormLibEnv :: LibEnv -> Result LibEnv
normalFormLibEnv le = normalFormLNS (getTopsortedLibs le) le

normalFormLNS :: [LibName] -> LibEnv -> Result LibEnv
normalFormLNS lns libEnv = foldM (\ le ln -> do
  let dg = lookupDGraph ln le
  newDg <- normalFormDG le dg
  return $ Map.insert ln
    (groupHistory dg normalFormRule newDg) le)
  libEnv lns

normalFormDG :: LibEnv -> DGraph -> Result DGraph
normalFormDG libEnv dgraph = foldM (\ dg (node, nodelab) ->
  if labelHasHiding nodelab then case dgn_nf nodelab of
    Just _ -> return dg -- already computed
    Nothing -> if isDGRef nodelab then do
        {- the normal form of the node
        is a reference to the normal form of the node it references
        careful: here not refNf, but a new Node which references refN -}
       let refLib = dgn_libname nodelab
           refNode = dgn_node nodelab
           refGraph' = lookupDGraph refLib libEnv
           refLabel = labDG refGraph' refNode
       case dgn_nf refLabel of
         Nothing -> warning dg
           (getDGNodeName refLabel ++ " (node " ++ show refNode
            ++ ") from '" ++ show (getLibId refLib)
            ++ "' without normal form") nullRange
         Just refNf -> do
           let refNodelab = labDG refGraph' refNf
               -- the label of the normal form ^
               nfNode = getNewNodeDG dg
               -- the new reference node in the old graph ^
               refLab = refNodelab
                 { dgn_name = extName "NormalForm" $ dgn_name nodelab
                 , dgn_nf = Just nfNode
                 , dgn_sigma = Just $ ide $ dgn_sign refNodelab
                 , nodeInfo = newRefInfo refLib refNf
                 , dgn_lock = Nothing }
               newLab = nodelab
                 { dgn_nf = Just nfNode,
                   dgn_sigma = dgn_sigma refLabel }
               chLab = SetNodeLab nodelab (node, newLab)
               changes = [InsertNode (nfNode, refLab), chLab]
               newGraph = changesDGH dgraph changes
           return newGraph
      else do
        let gd = insNode (node, dgn_theory nodelab) empty
            g0 = Map.fromList [(node, node)]
            (diagram, g) = computeDiagram dg [node] (gd, g0)
            fsub = finalSubcateg diagram
            Result ds res = gWeaklyAmalgamableCocone fsub
            es = map (\ d -> if isErrorDiag d then d { diagKind = Warning }
                             else d) ds
        appendDiags es
        case res of
          Nothing -> warning dg
                ("cocone failure for " ++ getDGNodeName nodelab
                 ++ " (node " ++ shows node ")") nullRange
          Just (sign, mmap) -> do
            {- we don't know that node is in fsub
            if it's not, we have to find a tip accessible from node
            and dgn_sigma = edgeLabel(node, tip); mmap (g Map.! tip) -}
            morNode <- if node `elem` nodes fsub then let
                        gn = Map.findWithDefault (error "gn") node g
                        phi = Map.findWithDefault (error "mor") gn mmap
                       in return phi else let
                          leaves = filter (\ x -> outdeg fsub x == 0) $
                                     nodes fsub
                          paths = map (\ x ->
                                       (x, propagateErrors "normalFormDG"
                                             $ dijkstra diagram node x))
                                      $ filter (\ x -> node `elem` predecs
                                                      diagram x) leaves
                                          in
                            case paths of
                             [] -> fail "node should reach a tip"
                             (xn, xf) : _ -> comp xf $ mmap Map.! xn
            let nfNode = getNewNodeDG dg -- new node for normal form
                info = nodeInfo nodelab
                ConsStatus c cp pr = node_cons_status info
                nfLabel = newInfoNodeLab
                  (extName "NormalForm" $ dgn_name nodelab)
                  info
                  { node_origin = DGNormalForm node
                  , node_cons_status = mkConsStatus c }
                  sign
                newLab = nodelab -- the new label for node
                     { dgn_nf = Just nfNode
                     , dgn_sigma = Just morNode
                     , nodeInfo = info
                         { node_cons_status = ConsStatus None cp pr }
                     }
            -- add the nf to the label of node
                chLab = SetNodeLab nodelab (node, newLab)
            -- insert the new node and add edges from the predecessors
                insNNF = InsertNode (nfNode, nfLabel)
                makeEdge src tgt m = (src, tgt, globDefLink m DGLinkProof)
                insStrMor = map (\ (x, f) -> InsertEdge $ makeEdge x nfNode f)
                  $ nubOrd $ map (\ (x, y) -> (g Map.! x, y))
                  $ (node, morNode) : Map.toList mmap
                allChanges = insNNF : chLab : insStrMor
                newDG = changesDGH dg allChanges
            return $ changeDGH newDG $ SetNodeLab nfLabel (nfNode, nfLabel
              { globalTheory = computeLabelTheory libEnv newDG
                (nfNode, nfLabel) })
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
       defInEdges = map (\ n -> (n, filter (\ e@(s, t, _) -> s /= t &&
                         liftE (liftOr isGlobalDef isHidingDef) e) $
                        innDG dgraph $ g Map.! n)) nodeList
       {- TO DO: no local links, and why edges with s=t are removed
       add normal form nodes
       sources of each edge must be added as new nodes -}
       nodeIds = zip (newNodes (length $ concatMap snd defInEdges) gd)
                     $ concatMap (\ (n, l) -> map (\ x -> (n, x)) l ) defInEdges
       newLNodes = zip (map fst nodeIds) $
                   map (\ (s, _, _) -> dgn_theory $ labDG dgraph s) $
                   concatMap snd defInEdges
       g0 = Map.fromList $
                     map (\ (newS, (_newT, (s, _t, _))) -> (newS, s)) nodeIds
       morphEdge (n1, (n2, (_, _, el))) =
         if isHidingDef $ dgl_type el
            then (n2, n1, (x, dgl_morphism el))
            else (n1, n2, (x, dgl_morphism el))
         where EdgeId x = dgl_id el
       newLEdges = map morphEdge nodeIds
       gd' = insEdges newLEdges $ insNodes newLNodes gd
       g' = Map.union g g0
   in computeDiagram dgraph (map fst nodeIds) (gd', g')

finalSubcateg :: GDiagram -> GDiagram
finalSubcateg graph = let
    leaves = filter (\ (n, _) -> outdeg graph n == 0) $ labNodes graph
 in buildGraph graph (map fst leaves) leaves [] $ nodes graph

predecs :: Gr a b -> Node -> [Node]
predecs graph node = let
   descs nList descList =
    case nList of
      [] -> descList
      _ -> let
             newDescs = concatMap (pre graph) nList
             nList' = filter (`notElem` nList) newDescs
             descList' = nubOrd $ descList ++ newDescs
           in descs nList' descList'
 in descs [node] []

buildGraph :: GDiagram -> [Node]
           -> [LNode G_theory]
           -> [LEdge (Int, GMorphism)]
           -> [Node]
           -> GDiagram
buildGraph oGraph leaves nList eList nodeList =
 case nodeList of
  [] -> mkGraph nList eList
  n : nodeList' ->
     case outdeg oGraph n of
      1 -> buildGraph oGraph leaves nList eList nodeList'
       -- the node is simply removed
      0 -> buildGraph oGraph leaves nList eList nodeList'
       -- the leaves have already been added to nList
      _ -> let
            Just l = lab oGraph n
            nList' = (n, l) : nList
            accesLeaves = filter (\ x -> n `elem` predecs oGraph x) leaves
            eList' = map (\ x -> (n, x, (1 :: Int,
                       propagateErrors "buildGraph" $ dijkstra oGraph n x)))
                       accesLeaves
           in buildGraph oGraph leaves nList' (eList ++ eList') nodeList'
       -- branch, must add n to the nList and edges in eList
