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

import Driver.Options (HetcatsOpts (outtypes), putIfVerbose)
import Driver.ReadFn
import Driver.AnaLib

import Static.DevGraph

import GUI.UDGUtils as UDG
import GUI.Utils

import GUI.GraphTypes
import GUI.GraphLogic (translateGraph)
import GUI.ShowLogicGraph (showLogicGraph)
import GUI.GraphDisplay
import qualified GUI.GraphAbstraction as GA

import Common.LibName
import qualified Common.Lib.Rel as Rel

import Data.IORef
import qualified Data.Map as Map

import Control.Concurrent.MVar
import Control.Monad (when)

import Interfaces.DataTypes
import Interfaces.Utils


type NodeEdgeList = ([DaVinciNode LibName], [DaVinciArc (IO String)])

{- | Creates a  new uDrawGraph Window and shows the Library Dependency Graph of
     the given LibEnv. -}
showLibGraph :: LibFunc
showLibGraph gInfo@(GInfo { windowCount = wc
                          , libGraphLock = lock}) = do
  isEmpty <- isEmptyMVar lock
  when isEmpty $ do
    putMVar lock ()
    count <- takeMVar wc
    putMVar wc $ count + 1
    graph <- newIORef daVinciSort
    nodesEdges <- newIORef (([], []) :: NodeEdgeList)
    let
      globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [ Button "Reload Library" $ reloadLibGraph gInfo graph nodesEdges
          , Button "Translate Library" $ translate gInfo
          , Button "Show Logic Graph" $ showLogicGraph daVinciSort
          ])
      graphParms = globalMenu $$
                   GraphTitle "Library Graph" $$
                   OptimiseLayout True $$
                   AllowClose (close gInfo) $$
                   FileMenuAct ExitMenuOption (Just (exit gInfo)) $$
                   emptyGraphParms
    graph' <- newGraph daVinciSort graphParms
    addNodesAndEdges gInfo graph' nodesEdges
    writeIORef graph graph'
    redraw graph'

-- | Reloads all Libraries and the Library Dependency Graph
reloadLibGraph :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeEdgeList
               -> IO ()
reloadLibGraph gInfo graph nodesEdges = do
  b <- warningDialog "Reload library" warnTxt
  when b $ reloadLibGraph' gInfo graph nodesEdges

warnTxt :: String
warnTxt = unlines
  [ "Are you sure to recreate Library?"
  , "All development graph windows will be closed and proofs will be lost."
  , "", "This operation can not be undone." ]

-- | Reloads all Libraries and the Library Dependency Graph
reloadLibGraph' :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeEdgeList
                -> IO ()
reloadLibGraph' gInfo@(GInfo { hetcatsOpts = opts
                             , libName = ln }) graph nodesEdges = do
  graph' <- readIORef graph
  (nodes, edges) <- readIORef nodesEdges
  let libfile = libNameToFile ln
  m <- anaLib opts { outtypes = [] } libfile
  case m of
    Nothing -> errorDialog "Error" $ "Error when reloading file '"
                                     ++ libfile ++ "'"
    Just (_, le) -> do
      closeOpenWindows gInfo
      mapM_ (deleteArc graph') edges
      mapM_ (deleteNode graph') nodes
      addNodesAndEdges gInfo graph' nodesEdges
      writeIORef graph graph'
      redraw graph'
      let ost = emptyIntState
          nwst = case i_state ost of
            Nothing -> ost
            Just ist -> ost { i_state = Just $ ist { i_libEnv = le
                                                   , i_ln = ln }
                            , filename = libfile }
      writeIORef (intState gInfo) nwst
      mShowGraph gInfo ln

-- | Translate Graph
translate :: GInfo -> IO ()
translate gInfo = do
  b <- warningDialog "Translate library" warnTxt
  when b $ translate' gInfo

-- | Translate Graph
translate' :: GInfo -> IO ()
translate' gInfo@(GInfo { libName = ln }) = do
  mle <- translateGraph gInfo
  case mle of
    Just le -> do
      closeOpenWindows gInfo
      let ost = emptyIntState
          nwst = case i_state ost of
            Nothing -> ost
            Just ist -> ost { i_state = Just $ ist { i_libEnv = le
                                                   , i_ln = ln }
                            , filename = libNameToFile ln }
      writeIORef (intState gInfo) nwst
      mShowGraph gInfo ln
    Nothing -> return ()

-- | Reloads the open graphs
closeOpenWindows :: GInfo -> IO ()
closeOpenWindows (GInfo { openGraphs = iorOpenGrpahs
                        , windowCount = wCount }) = do
  oGrpahs <- readIORef iorOpenGrpahs
  mapM_ (GA.closeGraphWindow . graphInfo) $ Map.elems oGrpahs
  writeIORef iorOpenGrpahs Map.empty
  takeMVar wCount
  putMVar wCount 1

-- | Adds the Librarys and the Dependencies to the Graph
addNodesAndEdges :: GInfo -> DaVinciGraphTypeSyn -> IORef NodeEdgeList -> IO ()
addNodesAndEdges gInfo@(GInfo { hetcatsOpts = opts}) graph nodesEdges = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    lookup' x y = Map.findWithDefault (error "lookup': node not found") y x
    keys = Map.keys le
    subNodeMenu = LocalMenu (UDG.Menu Nothing [
      Button "Show Graph" $ mShowGraph gInfo,
      Button "Show spec/View Names" $ showSpec le])
    subNodeTypeParms = subNodeMenu $$$
                       Box $$$
                       ValueTitle (return . show) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   subNodeList <- mapM (newNode graph subNodeType) keys
   let
    nodes' = Map.fromList $ zip keys subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle id $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (node1, node2) = newArc graph subArcType (return "")
                                            (lookup' nodes' node1)
                                            (lookup' nodes' node2)
   subArcList <- mapM insertSubArc $ getLibDeps le
   writeIORef nodesEdges (subNodeList, subArcList)

-- | Creates a list of all LibName pairs, which have a dependency
getLibDeps :: LibEnv -> [(LibName, LibName)]
getLibDeps = Rel.toList . Rel.intransKernel . getLibDepRel

mShowGraph :: GInfo -> LibName -> IO ()
mShowGraph gInfo@(GInfo {hetcatsOpts = opts}) ln = do
  putIfVerbose opts 3 "Converting Graph"
  gInfo' <- copyGInfo gInfo ln
  convertGraph gInfo' "Development Graph" showLibGraph
  let gi = graphInfo gInfo'
  GA.showTemporaryMessage gi "Development Graph initialized."
  return ()

-- | Displays the Specs of a Library in a Textwindow
showSpec :: LibEnv -> LibName -> IO ()
showSpec le ln =
  createTextDisplay ("Contents of " ++ show ln)
                    $ unlines . map show . Map.keys . globalEnv
                    $ lookupDGraph ln le

