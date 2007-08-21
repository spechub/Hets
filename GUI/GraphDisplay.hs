{- |
Module      :  $Header$
Description :  Central GUI for Hets, with display of development graph
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Conversion of development graphs from Logic.DevGraph
   to abstract graphs of the graph display interface

A composition table is used when abstracting the graph and composing
multiple edges. It looks like this

@
 [(\"normal\",\"normal\",\"normal\"),
 (\"normal\",\"inclusion\",\"normal\"),
 (\"inclusion\",\"normal\",\"normal\"),
 (\"inclusion\",\"inclusion\",\"inclusion\")]
@

A ginfo can be created with initgraphs. The graph is then created with
addnode and addlink.

-}

module GUI.GraphDisplay
    (convertGraph,initializeConverter)
    where

import Static.DevGraph

import GUI.AbstractGraphView as AGV
import GUI.GraphMenu
import GUI.GraphTypes
import GUI.GraphLogic(convertNodes, convertEdges)

import qualified HTk

import Data.IORef
import qualified Data.Map as Map(lookup)
import Control.Concurrent.MVar

initializeConverter :: IO (GInfo,HTk.HTk)
initializeConverter =
    do wishInst <- HTk.initHTk [HTk.withdrawMainWin]
       gInfo <- emptyGInfo
       return (gInfo,wishInst)

{- | converts the development graph given by its libname into an
    abstract graph and returns the descriptor of the latter, the
    graphInfo it is contained in and the conversion maps. -}
convertGraph :: ConvFunc
convertGraph gInfo@(GInfo {libEnvIORef = ioRefProofStatus,
                           gi_LIB_NAME = libname,
                           conversionMapsIORef = convRef,
                           windowCount = wc
                           }) title showLib = do
  libEnv <- readIORef ioRefProofStatus
  convMaps <- readIORef convRef
  case Map.lookup libname libEnv of
    Just dgraph -> do
      notopen <- isEmptyMVar $ openlock dgraph
      case notopen of
        True -> do
          putMVar (openlock dgraph) ()
          count <- takeMVar wc
          putMVar wc $ count + 1
          (abstractGraph,grInfo,_) <- initializeGraph gInfo dgraph title
                                      showLib
          if (isEmptyDG dgraph) then return (abstractGraph, grInfo,convMaps)
            else do
              newConvMaps <- convertNodes convMaps abstractGraph grInfo dgraph
                                          libname
              finalConvMaps <- convertEdges newConvMaps abstractGraph grInfo
                                            dgraph libname
              writeIORef convRef finalConvMaps
              return (abstractGraph, grInfo, finalConvMaps)
        False -> error $ "development graph with libname " ++ show libname
                         ++" is allready open"
    Nothing -> error $ "development graph with libname " ++ show libname
                       ++" does not exist"

-- | initializes an empty abstract graph with the needed node and edge types,
-- return type equals the one of convertGraph
initializeGraph :: GInfo -> DGraph -> String -> LibFunc
                -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph gInfo@(GInfo {conversionMapsIORef = convRef,
                              graphId = gid,
                              nextGraphId = nextId,
                              gi_LIB_NAME = ln,
                              gi_GraphInfo = actGraphInfo,
                              visibleNodesIORef = visibleNodesRef
                             }) dGraph title showLib = do
  writeIORef visibleNodesRef [(nodesDG dGraph)]
  let title' = (title ++ " for " ++ show ln)
  AGV.Result descr msg <- createGraph gInfo title' (convertGraph) (showLib)
  case msg of
    Nothing -> return ()
    Just err -> fail err
  writeIORef nextId $ gid + 1
  return (descr,actGraphInfo,convRef)

