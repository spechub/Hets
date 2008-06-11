{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  i.stassiy@jacobs-university.de
Stability   :  provisional
Portability :  non-portable(Logic)

In this module we introduce flattening of the graph. All the edges in the graph are cut out and theories of a node
with theories of all the incoming nodes are merged into a theory of a new node and then inserted in the graph.
While the old nodes are deleted.
-}

module Static.DGFlattening (updateNodeT,
	                    dg_flattening,
                            libEnv_flattening	
                            ) where
	

import Logic.Prover()
import Logic.Logic()
import Logic.Grothendieck()

import Static.DevGraph
import Static.GTheory()
import Static.DevGraph
import Static.DGToSpec()
import Proofs.EdgeUtils
import Proofs.TheoremHideShift

import Syntax.AS_Library
import Syntax.AS_Structured()

import Common.AS_Annotation()
import Common.Result

import Data.Graph.Inductive.Graph
import Data.Map
import qualified Data.Map as Map

import Control.Monad


updateNodeT :: LibEnv -> LIB_NAME -> Node -> Result (LNode DGNodeLab)
updateNodeT libEnv ln n =
 let
  g = lookupDGraph ln libEnv
  nodeLab = labDG g n
 in
  do
    (_le, ndgn_theory) <- computeTheory libEnv ln n
    return   (n , newInfoNodeLab (dgn_name nodeLab) (nodeInfo nodeLab) (ndgn_theory))

dg_flattening :: LibEnv -> LIB_NAME -> Result DGraph
dg_flattening libEnv ln = do
       let
                dg = lookupDGraph ln libEnv
                nds =  nodesDG dg
       upd_nodes <- mapM (\ x -> updateNodeT libEnv ln x) nds
       let      -- part for dealing with history
                l_nodes = labNodesDG dg
                l_edges = labEdgesDG dg
                change_de =  Prelude.map (\ x -> DeleteEdge(x)) l_edges
                change_dn =  Prelude.map (\ x -> DeleteNode(x)) l_nodes
       change_an <- mapM (\ x -> liftM InsertNode $ updateNodeT libEnv ln x ) nds
       let
                rule_n = Prelude.map ( const Flattening ) nds
                rule_e =  Prelude.map ( const Flattening ) l_edges
                hist =  [(rule_n ++ rule_n ++ rule_e, change_de ++ change_dn ++ change_an)]
                -- part for dealing with the graoh itself
       return $ applyProofHistory hist  dg --insNodesDG upd_nodes $ setProofHistoryDG hist (delLEdgesDG l_edges dg)
       where
           delLEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
           delLEdgesDG ed dg = case ed of
             [] -> dg
             hd : tl -> delLEdgesDG tl ( delLEdgeDG hd dg )


libEnv_flattening :: LibEnv -> Result LibEnv
libEnv_flattening lib = do
        new_lib_env <- mapM (\ (x,_) -> do
                         z <- dg_flattening lib x
                         return (x, z)) $ Map.toList lib
        return $ Map.fromList new_lib_env



	
