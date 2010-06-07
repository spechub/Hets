{- |
Module      :  $Header$
Copyright   :  (c) Mihai Codescu, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mihai.codescu@dfki.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.ShowRefTree (showRefTree) where

import Control.Concurrent.MVar
import Control.Monad

import Data.Graph.Inductive.Graph as Tree
import Data.IORef

import GUI.GraphTypes
import GUI.UDGUtils as UDG

import Interfaces.DataTypes

import Static.DevGraph

import qualified Data.Map as Map

showRefTree :: LibFunc
showRefTree gInfo@(GInfo { windowCount = wc}) = do
  -- isEmpty <- isEmptyMVar lock
  -- when isEmpty $ do
  -- putMVar lock ()
    count <- takeMVar wc
    putMVar wc $ count + 1
    graph <- newIORef daVinciSort
    nodesEdges <- newIORef (([], []) :: NodeEdgeListRef)
    let
      globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [])
      graphParms = globalMenu $$
                   GraphTitle "Refinement Tree" $$
                   OptimiseLayout True $$
                   AllowClose (closeGInfo gInfo) $$
                   FileMenuAct ExitMenuOption (Just (exitGInfo gInfo)) $$
                   emptyGraphParms
    graph' <- newGraph daVinciSort graphParms
    addNodesAndEdgesRef gInfo graph' nodesEdges
    writeIORef graph graph'
    redraw graph'

type NodeEdgeListRef = ([DaVinciNode RTNodeLab], [DaVinciArc (IO RTLinkLab)])
type NodeEdgeListDep = ([DaVinciNode DiagNodeLab], [DaVinciArc (IO String)])

addNodesAndEdgesRef :: GInfo -> DaVinciGraphTypeSyn ->
                       IORef NodeEdgeListRef -> IO ()
addNodesAndEdgesRef gInfo@(GInfo { hetcatsOpts = opts}) graph nodesEdges = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    lookup' x y = Map.findWithDefault (error "lookup': node not found") y x
    dg = lookup' le $ i_ln ist
    rTree = refTree dg
    vertexes = map snd $ Tree.labNodes rTree
    arcs = Tree.labEdges rTree
    subNodeMenu = LocalMenu (UDG.Menu Nothing [
                   Button "Show dependency diagram" $ showDiagram gInfo dg])
    subNodeTypeParms = subNodeMenu $$$
                       Ellipse $$$
                       ValueTitle (return . rtn_name) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   subNodeList <- mapM (newNode graph subNodeType) vertexes
   let
    nodes' = Map.fromList $ zip (Tree.nodes rTree) subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
    subArcTypeParmsT = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Blue False False) $$$
                      emptyArcTypeParms
    subArcTypeParmsR = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Coral False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (n1, n2, e) = newArc graph subArcType
                                            (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcList <- mapM insertSubArc $
                    filter (\ (_, _, e) -> rtl_type e == RTComp) arcs
   subArcTypeT <- newArcType graph subArcTypeParmsT
   let insertSubArcT (n1, n2, e) = newArc graph subArcTypeT
                                            (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcListT <- mapM insertSubArcT $
                    filter (\ (_, _, e) -> rtl_type e == RTTyping) arcs
   subArcTypeR <- newArcType graph subArcTypeParmsR
   let insertSubArcR (n1, n2, e) = newArc graph subArcTypeR
                                            (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcListR <- mapM insertSubArcR $
                    filter (\ (_, _, e) -> rtl_type e == RTRefine) arcs
   writeIORef nodesEdges (subNodeList, subArcList ++ subArcListT ++ subArcListR)

showDiagram :: GInfo -> DGraph -> RTNodeLab -> IO ()
showDiagram gInfo@(GInfo { windowCount = wc}) dg rtlab = do
 let asDiags = archSpecDiags dg
     name = rtn_name rtlab
 when (name `elem` Map.keys asDiags) $ do
      count <- takeMVar wc
      putMVar wc $ count + 1
      graph <- newIORef daVinciSort
      nodesEdges <- newIORef (([], []) :: NodeEdgeListDep)
      let
       globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [])
       graphParms = globalMenu $$
                   GraphTitle ("Dependency Diagram for " ++ name) $$
                   OptimiseLayout True $$
                   AllowClose (closeGInfo gInfo) $$
                   FileMenuAct ExitMenuOption (Just (exitGInfo gInfo)) $$
                   emptyGraphParms
      graph' <- newGraph daVinciSort graphParms
      addNodesAndEdgesDeps (Map.findWithDefault (error "showDiagram")
                            name asDiags)
                           graph' gInfo nodesEdges
      writeIORef graph graph'
      redraw graph'

addNodesAndEdgesDeps :: Diag -> DaVinciGraphTypeSyn -> GInfo ->
                       IORef NodeEdgeListDep -> IO ()
addNodesAndEdgesDeps diag graph
  _gInfo@(GInfo { hetcatsOpts = opts}) nodesEdges = do
   let
    lookup' x y = Map.findWithDefault (error "lookup': node not found") y x
    vertexes = map snd $ Tree.labNodes $ diagGraph diag
    arcs = Tree.labEdges $ diagGraph diag
    subNodeMenu = LocalMenu (UDG.Menu Nothing [])
    subNodeTypeParms = subNodeMenu $$$
                       Ellipse $$$
                       ValueTitle (return . dn_desc) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   subNodeList <- mapM (newNode graph subNodeType) vertexes
   let
    nodes' = Map.fromList $ zip (Tree.nodes $ diagGraph diag) subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (n1, n2, _e) = newArc graph subArcType
                                            (return "")
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcList <- mapM insertSubArc arcs
   writeIORef nodesEdges (subNodeList, subArcList)
