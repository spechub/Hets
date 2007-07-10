{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@tzi.de
Stability   :  unstable
Portability :  non-portable

This Modul provides a function to display a Library Dependency Graph. Just the ShowLibGraph function is exported.

-}

module GUI.ShowLibGraph
  (showLibGraph,mShowGraph)
where

import Driver.Options(HetcatsOpts(outtypes),putIfVerbose)
import Driver.ReadFn

import Syntax.AS_Library

import Static.DevGraph
import Static.AnalysisLibrary

-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay
import Configuration

import GUI.GraphTypes
import GUI.GraphLogic(getLibDeps, hideNodes)
import GUI.GraphDisplay
import GUI.AbstractGraphView

import Data.IORef
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

type NodeArcList = ([DaVinciNode LIB_NAME],[DaVinciArc (IO String)])

{- | Creates a  new uDrawGraph Window and shows the Library Dependency Graph of
     the given LibEnv.-}
showLibGraph :: LibFunc
showLibGraph gInfo = do
  depGRef <- newIORef daVinciSort
  nodeArcRef <- newIORef (([],[])::NodeArcList)
  let
    globalMenu = GlobalMenu (Menu Nothing [
                   Button "Reload Libraries" 
                     (reload gInfo depGRef nodeArcRef)
                   ])
    graphParms = globalMenu $$
                 GraphTitle "Library Graph" $$
	         OptimiseLayout True $$
	         AllowClose (return True) $$
		 emptyGraphParms
  depG <- newGraph daVinciSort graphParms
  addNodesAndArcs gInfo depG nodeArcRef
  writeIORef depGRef depG
  redraw depG
  return depG

-- | Reloads all Libraries and the Library Dependency Graph
reload :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeArcList -> IO()
reload gInfo@(GInfo {gi_LIB_NAME = ln,
                     gi_hetcatsOpts = opts
                    }) depGRef nodeArcRef = do
  depG <- readIORef depGRef
  (nodes', arcs) <- readIORef nodeArcRef
  let
    libfile = libNameToFile opts ln
  m <- anaLib opts { outtypes = [] } libfile
  case m of
    Nothing -> fail $
      "Could not read original development graph from '" ++ libfile ++  "'"
    Just (_, _) -> do
      mapM_ (deleteArc depG) arcs
      mapM_ (deleteNode depG) nodes'
      addNodesAndArcs gInfo depG nodeArcRef
      writeIORef depGRef depG
      redraw depG

-- | Adds the Librarys and the Dependencies to the Graph
addNodesAndArcs :: GInfo -> DaVinciGraphTypeSyn -> IORef NodeArcList -> IO ()
addNodesAndArcs gInfo@(GInfo {libEnvIORef = ioRefProofStatus}) depG
  nodeArcRef = do
  le <- readIORef ioRefProofStatus
  let
    lookup' x y = Map.findWithDefault (error "lookup': node not found") y x
    keys = Map.keys le
    subNodeMenu = LocalMenu( Menu Nothing [
      Button "Show Graph" $ mShowGraph gInfo, 
      Button "Show spec/View Names" $ showSpec le])
    subNodeTypeParms = subNodeMenu $$$
                       Box $$$
                       ValueTitle (\ x -> return (show x)) $$$
                       Color "green" $$$
                       emptyNodeTypeParms
  subNodeType <- newNodeType depG subNodeTypeParms
  subNodeList <- mapM (newNode depG subNodeType) keys
  let
    nodes' = Map.fromList $ zip keys subNodeList
    subArcMenu = LocalMenu( Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle id $$$
                      Color "black" $$$
                      emptyArcTypeParms
  subArcType <- newArcType depG subArcTypeParms
  let
    insertSubArc = \ (node1, node2) -> newArc depG subArcType (return "")
                       (lookup' nodes' node1) (lookup' nodes' node2)
  subArcList <- mapM insertSubArc $  Rel.toList $ Rel.intransKernel $ 
    Rel.transClosure $ Rel.fromList $ getLibDeps le
  writeIORef nodeArcRef (subNodeList, subArcList)

-- | Displays the Specs of a Library in a Textwindow
mShowGraph :: GInfo -> LIB_NAME -> IO()
mShowGraph gInfo@(GInfo {gi_hetcatsOpts = opts,
                        gi_GraphInfo = actGraphInfo
                       }) ln = do
  putIfVerbose opts 3 "Converting Graph"
  (_,next) <- readIORef actGraphInfo
  let gInfo' = gInfo {gi_LIB_NAME = ln,
                      graphId = next}
  (gid,gv,_) <- convertGraph gInfo' "Development Graph" showLibGraph
  redisplay gid gv
  hideNodes gInfo'
  layoutImproveAll gid gv
  redisplay gid gv
  return ()

-- | Displays the Specs of a Library in a Textwindow
showSpec :: LibEnv -> LIB_NAME -> IO()
showSpec le ln = do
  let
    ge = globalEnv $ lookupGlobalContext ln le
    sp = unlines $ map show $ Map.keys $ ge
  createTextDisplay ("Contents of " ++ (show ln)) sp [size(80,25)]
