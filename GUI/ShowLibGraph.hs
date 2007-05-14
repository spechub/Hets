{-# OPTIONS -cpp #-}
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
  (showLibGraph, getLibDeps)
where

import Driver.Options(HetcatsOpts(outtypes))
import Driver.ReadFn

import Syntax.AS_Library

import ATC.AS_Library()

import Static.DevGraph
import Static.AnalysisLibrary

-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay
import Configuration

import Data.IORef
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree

import Data.List

type DaVinciGraphTypeSyn = Graph DaVinciGraph 
   DaVinciGraphParms DaVinciNode DaVinciNodeType DaVinciNodeTypeParms
   DaVinciArc DaVinciArcType DaVinciArcTypeParms

type NodeArcList = ([DaVinciNode LIB_NAME],[DaVinciArc (IO String)])

{- | Creates a  new uDrawGraph Window and shows the Library Dependency Graph of
     the given LibEnv.-}
showLibGraph :: HetcatsOpts -> LIB_NAME ->  LibEnv
             -> (String -> LIB_NAME -> IO()) -> IO ()
showLibGraph opts ln le showGraph =
  do
    depGRef <- newIORef daVinciSort
    nodeArcRef <- newIORef (([],[])::NodeArcList)
    let
      globalMenu = GlobalMenu (Menu Nothing [
                     Button "Reload Libraries" 
                       (reload opts ln showGraph depGRef nodeArcRef)
                     ])
      graphParms = globalMenu $$
                   GraphTitle "Library Graph" $$
		   OptimiseLayout True $$
		   AllowClose (return True) $$
		   emptyGraphParms
    depG <- newGraph daVinciSort graphParms
    addNodesAndArcs le showGraph depG nodeArcRef
    writeIORef depGRef depG
    redraw depG

-- | Reloads all Libraries and the Library Dependency Graph
reload :: HetcatsOpts -> LIB_NAME -> (String -> LIB_NAME -> IO())
       -> IORef DaVinciGraphTypeSyn -> IORef NodeArcList -> IO()
reload opts ln showGraph depGRef nodeArcRef = 
  do
    depG <- readIORef depGRef
    (nodes, arcs) <- readIORef nodeArcRef
    let
      libfile = libNameToFile opts ln
    m <- anaLib opts { outtypes = [] } libfile
    case m of
      Nothing -> fail
        $ "Could not read original development graph from '"
        ++ libfile ++  "'"
      Just (_, le) -> do
        mapM_ (deleteArc depG) arcs
        mapM_ (deleteNode depG) nodes
        addNodesAndArcs le showGraph depG nodeArcRef
        writeIORef depGRef depG
        redraw depG

-- | Adds the Librarys and the Dependencies to the Graph
addNodesAndArcs :: LibEnv -> (String -> LIB_NAME -> IO())
                -> DaVinciGraphTypeSyn -> IORef NodeArcList -> IO ()
addNodesAndArcs le showGraph depG nodeArcRef =
  do
    let
      lookup' x y = Map.findWithDefault
                    (error "lookup': node not found")
                    y x
      keys = Map.keys le
      subNodeMenu = LocalMenu( Menu Nothing [
        Button "Show Graph" $
          showGraph "Development Graph", 
        Button "Show spec/View Names" (showSpec le)])
      subNodeTypeParms = subNodeMenu $$$
			 Box $$$
			 ValueTitle (\ x -> return (show x)) $$$
			 Color "green" $$$
			 emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    subNodeList <- mapM (newNode depG subNodeType) keys
    let
      nodes = Map.fromList $ zip keys subNodeList
      subArcMenu = LocalMenu( Menu Nothing [])
      subArcTypeParms = subArcMenu $$$
                        ValueTitle id $$$
                        Color "black" $$$
                        emptyArcTypeParms
    subArcType <- newArcType depG subArcTypeParms
    let
      insertSubArc = \ (node1, node2) ->
                          newArc depG subArcType (return "")
                            (lookup' nodes node1)
                            (lookup' nodes node2)
    subArcList <- mapM insertSubArc $
      Rel.toList $ Rel.intransKernel $ Rel.transClosure $
      Rel.fromList $ getLibDeps le
    writeIORef nodeArcRef (subNodeList, subArcList)

-- | Displays the Specs of a Library in a Textwindow
showSpec :: LibEnv -> LIB_NAME -> IO()
showSpec le ln =
  do
    let
      ge = globalEnv $ lookupGlobalContext ln le
      sp = unlines $ map show $ Map.keys $ ge
    createTextDisplay ("Contents of " ++ (show ln)) sp [size(80,25)]

-- | Creates a list of all LIB_NAME pairs, which have a dependency
getLibDeps :: LibEnv -> [(LIB_NAME, LIB_NAME)]
getLibDeps le =
  concat $ map (\ ln -> getDep ln le) $ Map.keys le

-- | Creates a list of LIB_NAME pairs for the fist argument 
getDep :: LIB_NAME -> LibEnv -> [(LIB_NAME, LIB_NAME)]
getDep ln le =
  map (\ x -> (ln, x)) $ map (\ (_,x,_) -> dgn_libname x) $ IntMap.elems $
    IntMap.filter (\ (_,x,_) -> isDGRef x) $ Tree.convertToMap $ 
    devGraph $ lookupGlobalContext ln le
