{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  unstable
Portability :  non-portable

This Modul provides a function to display a Library Dependency Graph.
-}

module GUI.ShowLibGraph (showLibGraph, mShowGraph) where

import Driver.Options (HetcatsOpts(outtypes), putIfVerbose)
import Driver.ReadFn
import Driver.AnaLib

import Static.DevGraph

import GUI.UDGUtils as UDG
import GUI.HTkUtils

import GUI.GraphTypes
import GUI.GraphLogic(getLibDeps, hideNodes)
import GUI.GraphDisplay
import qualified GUI.GraphAbstraction as GA

import Common.LibName
import qualified Common.Lib.Rel as Rel

import Data.IORef
import qualified Data.Map as Map

import Control.Concurrent.MVar
import Control.Concurrent(threadDelay)

import Interfaces.DataTypes

type NodeArcList = ([DaVinciNode LIB_NAME],[DaVinciArc (IO String)])

{- | Creates a  new uDrawGraph Window and shows the Library Dependency Graph of
     the given LibEnv.-}
showLibGraph :: LibFunc
showLibGraph gInfo@(GInfo {windowCount = wc}) = do
  count <- takeMVar wc
  putMVar wc $ count + 1
  depGRef <- newIORef daVinciSort
  nodeArcRef <- newIORef (([],[])::NodeArcList)
  let
    globalMenu = GlobalMenu (UDG.Menu Nothing [
                   Button "Reload Libraries"
                     (reload gInfo depGRef nodeArcRef)
                   ])
    graphParms = globalMenu $$
                 GraphTitle "Library Graph" $$
                 OptimiseLayout True $$
                 AllowClose (close gInfo) $$
                 FileMenuAct ExitMenuOption (Just (exit gInfo)) $$
                 emptyGraphParms
  depG <- newGraph daVinciSort graphParms
  addNodesAndArcs gInfo depG nodeArcRef
  writeIORef depGRef depG
  redraw depG
  return depG

-- | Reloads all Libraries and the Library Dependency Graph
reload :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeArcList -> IO()
reload gInfo@(GInfo {gi_hetcatsOpts = opts
                    }) depGRef nodeArcRef = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let ln = i_ln ist
   depG <- readIORef depGRef
   (nodes', arcs) <- readIORef nodeArcRef
   let
    libfile = libNameToFile opts ln
   m <- anaLib opts { outtypes = [] } libfile
   case m of
    Nothing -> fail $
      "Error when reloading file '" ++ libfile ++  "'"
    Just (_, _) -> do
      mapM_ (deleteArc depG) arcs
      mapM_ (deleteNode depG) nodes'
      addNodesAndArcs gInfo depG nodeArcRef
      writeIORef depGRef depG
      redraw depG

-- | Adds the Librarys and the Dependencies to the Graph
addNodesAndArcs :: GInfo -> DaVinciGraphTypeSyn -> IORef NodeArcList -> IO ()
addNodesAndArcs gInfo@(GInfo { gi_hetcatsOpts = opts}) depG nodeArcRef = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    lookup' x y = Map.findWithDefault (error "lookup': node not found") y x
    keys = Map.keys le
    subNodeMenu = LocalMenu(UDG.Menu Nothing [
      Button "Show Graph" $ mShowGraph gInfo,
      Button "Show spec/View Names" $ showSpec le])
    subNodeTypeParms = subNodeMenu $$$
                       Box $$$
                       ValueTitle (\ x -> return (show x)) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType depG subNodeTypeParms
   subNodeList <- mapM (newNode depG subNodeType) keys
   let
    nodes' = Map.fromList $ zip keys subNodeList
    subArcMenu = LocalMenu(UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle id $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType depG subArcTypeParms
   let
    insertSubArc = \ (node1, node2) -> newArc depG subArcType (return "")
                       (lookup' nodes' node1) (lookup' nodes' node2)
   subArcList <- mapM insertSubArc $  Rel.toList $ Rel.intransKernel $
    Rel.transClosure $ Rel.fromList $ getLibDeps le
   writeIORef nodeArcRef (subNodeList, subArcList)

mShowGraph :: GInfo -> LIB_NAME -> IO()
mShowGraph gInfo@(GInfo {gi_hetcatsOpts = opts}) ln = do
  putIfVerbose opts 3 "Converting Graph"
  gInfo' <- copyGInfo gInfo ln
  convertGraph gInfo' "Development Graph" showLibGraph
  let gv = gi_GraphInfo gInfo'
  GA.deactivateGraphWindow gv
  hideNodes gInfo'
  GA.redisplay gv
  threadDelay 2000000
  GA.layoutImproveAll gv
  GA.showTemporaryMessage gv "Development Graph initialized."
  GA.activateGraphWindow gv
  return ()

-- | Displays the Specs of a Library in a Textwindow
showSpec :: LibEnv -> LIB_NAME -> IO()
showSpec le ln = do
  let
    ge = globalEnv $ lookupDGraph ln le
    sp = unlines $ map show $ Map.keys $ ge
  createTextDisplay ("Contents of " ++ show ln) sp [size(80,25)]

close :: GInfo -> IO Bool
close (GInfo { exitMVar = exit'
             , windowCount = wc
             }) = do
  count <- takeMVar wc
  case count == 1 of
    True -> putMVar exit' ()
    False -> putMVar wc $ count - 1
  return True

exit :: GInfo -> IO ()
exit (GInfo {exitMVar = exit'}) = do
  putMVar exit' ()
