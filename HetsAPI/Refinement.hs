{- |
Description :  HetsAPIs interface for refinment trees.
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.Refinement (
    RefinementTreeNode(..),
    RefinementTreeLink(..),
    getRefinementTree,
    getAvailableSpecificationsForRefinement
)

where

import Static.DevGraph (DGraph (specRoots), RTNodeLab, RTLinkLab, refTree, rtl_type, RTLinkType (..))

import qualified Common.Lib.Graph as Graph
import Data.Graph.Inductive (mkGraph, Node, suc, subgraph, labNodes, out, inn, labEdges, LNode, LEdge, nodes)
import qualified Data.Map as Map
import qualified Data.Set as Set

data RefinementTreeNode = RefinementTreeNode {
        isRootNode :: !Bool,
        rtNodeLab :: !RTNodeLab
    }

getRefinementTreeNode :: Graph.Gr RTNodeLab RTLinkLab -> LNode RTNodeLab -> LNode RefinementTreeNode
getRefinementTreeNode graph (x, lab) = (x, RefinementTreeNode (isRoot x graph) lab)

type RefinementTreeLink = RTLinkLab

getRefinementTreeEdge' :: (RTLinkLab -> Bool)
    -> [LEdge RTLinkLab]
    -> [LEdge RefinementTreeLink]
getRefinementTreeEdge' fn = filter (\ (_, _, e) -> fn e)

roots :: String -> DGraph -> Maybe (Set.Set Node)
roots rspName = fmap Set.fromList . Map.lookup rspName . specRoots

isRoot :: Node -> Graph.Gr a RTLinkLab -> Bool
isRoot n rTree = any (\ (_, _, llab) -> rtl_type llab == RTComp) (
            out rTree n) && not
            (any (\ (_, _, llab) -> rtl_type llab == RTComp) $
            inn rTree n)

ccomp :: String -> DGraph -> Maybe (Set.Set Node)
ccomp rspName dg = do
    roots' <- roots rspName dg
    return $ getConnectedComps roots' $ refTree dg

getConnectedComps :: Set.Set Node -> Graph.Gr a b -> Set.Set Node
getConnectedComps nodes0 tree =
    let nodes1 = Set.unions $ Set.map (Set.fromList . suc tree) nodes0 in
        if Set.isSubsetOf nodes1 nodes0
        then nodes0
        else getConnectedComps (foldl (flip Set.insert) nodes0 nodes1) tree

getRefinementTree :: String -> DGraph -> Maybe (Graph.Gr RefinementTreeNode RefinementTreeLink)
getRefinementTree rspName dg = do
    ccomp' <- Set.toList <$> ccomp rspName dg
    let
        nods = map (getRefinementTreeNode $ refTree dg) vertices
        nodeAliases = Map.fromList $ zip (nodes rTree) (fst <$> nods)
        rTree = subgraph ccomp' (refTree dg)
        vertices = labNodes rTree
        arcs = labEdges rTree
        edges' = arcListR ++ arcListC
        edges = [( nodeAliases Map.! s, nodeAliases Map.! t, l) | (s, t, l) <- edges']
        arcListR = getRefinementTreeEdge' ((==) RTComp . rtl_type) arcs
        arcListC = getRefinementTreeEdge' ((==) RTRefine . rtl_type) arcs
    return $ mkGraph nods edges

getAvailableSpecificationsForRefinement :: DGraph -> [String]
getAvailableSpecificationsForRefinement = Map.keys . specRoots
