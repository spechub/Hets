{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Interface for graph viewing and abstraction
Copyright   :  (c) Thiemo Wiedemeyer, T. Mossakowski, Uni Bremen 2002-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (relies on Logic via DevGraph)

Interface for graph viewing and abstraction.
-}

module GUI.GraphAbstraction
    ( -- * Types
      NodeValue
    , EdgeValue
    , NodeId
    , GraphInfo
    , AbstractionGraph
    -- * Creation and display
    , initgraphs
    , makegraph
    , makegraphExt
    , redisplay
    , showAll
    , clear
    -- * Node interface
    , addNode
    , delNode
    , hideNodes
    , isHiddenNode
    , hasHiddenNodes
    , changeNodeType
    , focusNode
    -- * Edge interface
    , addEdge
    , delEdge
    , hideEdge
    , hideSetOfEdgeTypes
    , isHiddenEdge
    , hasHiddenEdges
    , changeEdgeType
    -- * Direct manipulation of uDrawGraph
    , layoutImproveAll
    , showTemporaryMessage
    , deactivateGraphWindow
    , activateGraphWindow
    , closeGraphWindow
    ) where

import GUI.UDGUtils
#ifdef UNIVERSION2
import qualified UDrawGraph.Types as DVT
import Reactor.BSem
#else
import qualified DaVinciTypes as DVT
import BSem
#endif

import ATC.DevGraph ()
import Static.DevGraph (DGLinkLab, EdgeId(..),DGEdgeType,DGNodeType)

import Data.IORef
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LEdge)
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Maybe (isNothing)

import Control.Monad (filterM, unless)
import Control.Concurrent (threadDelay)

type OurGraph =
     Graph   DaVinciGraph
             DaVinciGraphParms
             DaVinciNode
             DaVinciNodeType
             DaVinciNodeTypeParms
             DaVinciArc
             DaVinciArcType
             DaVinciArcTypeParms

type NodeId = Int

type NodeValue = (String, NodeId)
type EdgeValue = (String, EdgeId, Maybe (LEdge DGLinkLab))

-- | Internal node
data GANode = GANode
  { udgNode :: Maybe (DaVinciNode NodeValue) -- ^ uDrawGraph node
  , ganType :: DGNodeType -- ^ ID of nodetype
  , ganValue :: NodeValue -- ^ Holds the nodevalue for uDrawGraph node
  }

-- | Internal edge
data GAEdge = GAEdge
  { udgEdge :: Maybe (DaVinciArc EdgeValue) -- ^ uDrawGraph edge
  , ganFrom :: NodeId -- ^ ID of source node
  , ganTo :: NodeId -- ^ID of target node
  , gaeType :: DGEdgeType -- ^ ID of edgetype
  , gaeValue :: EdgeValue -- ^ Holds the edgevalue for uDrawGraph edge
  }

data GANodeType = GANodeType
  { udgNodeType :: DaVinciNodeType NodeValue
  }

data GAEdgeType = GAEdgeType
  { udgEdgeType :: DaVinciArcType EdgeValue
  , udgCompressed :: (DaVinciArcType EdgeValue, DaVinciArcType EdgeValue)
  , gaeHidden :: Bool
  }

-- Main datastructure for carrying around the graph,
-- both internally (nodes as integers), and at the daVinci level
data AbstractionGraph = AbstractionGraph
  { theGraph :: OurGraph
  , nodes :: Map.Map NodeId GANode
  , edges :: Map.Map EdgeId GAEdge
  , nodeTypes :: Map.Map DGNodeType GANodeType
  , edgeTypes :: Map.Map DGEdgeType GAEdgeType
  , compressedEdges :: [GAEdge]
  }

type GraphInfo = IORef AbstractionGraph

instance Eq (DaVinciNode NodeValue) where
    (==) = eq1

instance Eq (DaVinciArc EdgeValue) where
    (==) = eq1

-- | Forces a redraw of the uDrawGraph and wait an amount of time
redisplay :: GraphInfo -> IO ()
redisplay gi = do
  g <- readIORef gi
  redraw (theGraph g)
  threadDelay 300000

clear :: GraphInfo -> IO ()
clear gi = do
  g <- readIORef gi
  mapM_ (delCompressedEdge gi) $ compressedEdges g
  writeIORef gi g { compressedEdges = [] }
  mapM_ (delEdge gi) $ Map.keys $ edges g
  mapM_ (delNode gi) $ Map.keys $ nodes g

-- | Creates an empty graph structure
graphtool :: OurGraph
graphtool = daVinciSort

-- | Creates the empty AbstractionGraph
initgraphs :: IO GraphInfo
initgraphs = do
  let g = AbstractionGraph
            { theGraph = graphtool
            , nodes = Map.empty
            , edges = Map.empty
            , nodeTypes = Map.empty
            , edgeTypes = Map.empty
            , compressedEdges = []
            }
  newIORef g

-- | Simpler version of makegraphExt
makegraph :: GraphInfo -- ^ The graph
          -> String        -- Title
          -> Maybe (IO ()) -- FileOpen Menu
          -> Maybe (IO ()) -- FileSave Menu
          -> Maybe (IO ()) -- FileSaveAs Menu
          -> [GlobalMenu]
          -> [(DGNodeType,DaVinciNodeTypeParms NodeValue)]
          -> [(DGEdgeType,DaVinciArcTypeParms EdgeValue)]
          -> IO ()
makegraph gi title open save saveAs menus nodetypeparams edgetypeparams =
  makegraphExt gi title open save saveAs (return True) Nothing menus
               nodetypeparams edgetypeparams

-- | Creates the uDrawGraph graph
makegraphExt :: GraphInfo -- ^ The graph
             -> String     -- Title
             -> Maybe (IO ()) -- FileOpen Menu
             -> Maybe (IO ()) -- FileSave Menu
             -> Maybe (IO ()) -- FileSaveAs Menu
             -> IO Bool       -- FileClose Menu
             -> Maybe (IO ()) -- FileExit Menu
             -> [GlobalMenu]
             -> [(DGNodeType,DaVinciNodeTypeParms NodeValue)]
             -> [(DGEdgeType,DaVinciArcTypeParms EdgeValue)]
             -> IO ()
makegraphExt gi title open save saveAs close exit menus nTypeParams
             eTypeParams = do
  let graphParms  =
        foldr ($$) (GraphTitle title $$
                    OptimiseLayout False $$
                    AllowClose close $$
                    FileMenuAct OpenMenuOption open $$
                    FileMenuAct SaveMenuOption save $$
                    FileMenuAct SaveAsMenuOption saveAs $$
                    FileMenuAct ExitMenuOption exit $$
                    emptyGraphParms)
                    menus
      (nTypeNames,nTypeParams') = unzip nTypeParams
      (eTypeNames,eTypeParams') = unzip eTypeParams
      eTypeParamsCO = map (LocalMenu (Button "Expand" (\ _ -> do
                                                       showAll gi
                                                       redisplay gi)) $$$)
                          eTypeParams'
      eTypeParamsCP = map (LocalMenu (Button "Expand" (\ _ -> do
                                                       showAll gi
                                                       redisplay gi)) $$$)
                     $ map (Color "purple2" $$$) eTypeParams'
  graph <- newGraph graphtool graphParms
  nTypes <- mapM (newNodeType graph) nTypeParams'
  eTypes <- mapM (newArcType graph) eTypeParams'
  cTypesO <- mapM (newArcType graph) eTypeParamsCO
  cTypesP <- mapM (newArcType graph) eTypeParamsCP
  let g = AbstractionGraph
            { theGraph = graph
            , nodes = Map.empty
            , edges = Map.empty
            , nodeTypes = Map.fromList $ zip nTypeNames
                $ map (\ nt -> GANodeType { udgNodeType = nt }) nTypes
            , edgeTypes = Map.fromList $ zip eTypeNames
                $ map (\ (et,ctO,ctP) -> GAEdgeType { udgEdgeType = et
                                                    , udgCompressed = (ctO,ctP)
                                                    , gaeHidden = False })
                $ zip3 eTypes cTypesO cTypesP
            , compressedEdges = []
            }
  writeIORef gi g

{- similar to lookup (for Map), but returns just the value if lookup was
   successful otherwise an error is raised. -}
get :: (Show k, Ord k) => k -> Map.Map k a -> a
get key = Map.findWithDefault (error $ "get: id unknown: " ++ show key) key

-- | Shows all hidden nodes and edges
showAll :: GraphInfo -- ^ The graph
        -> IO ()
showAll gi = do
  g <- readIORef gi
  mapM_ (delCompressedEdge gi) $ compressedEdges g
  writeIORef gi g { compressedEdges = [] }
  nodes' <- filterM (isHiddenNode gi) $ Map.keys $ nodes g
  edges' <- filterM (isHiddenEdge gi) $ Map.keys $ edges g
  mapM_ (showNode gi) nodes'
  mapM_ (showEdge gi) edges'

{- Functions for adding, deleting, changing and hidding nodes.-}

-- | Adds a node (type id)
addNode :: GraphInfo -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> DGNodeType -- ^ ID of the nodetype
        -> String -- ^ Name of the node
        -> IO ()
addNode gi nId nType nName = do
  g' <- readIORef gi
  g <- if Map.member nId $ nodes g' then do
      delNode gi nId
      readIORef gi
    else return g'
  node' <- newNode (theGraph g) (udgNodeType $ get nType $ nodeTypes g)
                   (nName,nId)
  let node = GANode { udgNode = Just node'
                    , ganType = nType
                    , ganValue = (nName, nId)
                    }
  writeIORef gi g { nodes = Map.insert nId node $ nodes g }

-- | Deletes a node
delNode :: GraphInfo -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> IO ()
delNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Just node -> deleteNode (theGraph g) node
    Nothing -> return ()
  writeIORef gi g { nodes = Map.delete nId $ nodes g }

-- | Hides a node
hideNode :: GraphInfo -- ^ The graph
         -> NodeId -- ^ ID of the node
         -> IO ()
hideNode gi nId = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case udgNode node of
    Nothing -> return ()
    Just node' -> do
      deleteNode (theGraph g) node'
      writeIORef gi g
        { nodes = Map.insert nId node {udgNode = Nothing} $ nodes g }

-- | Hides a set of nodes
hideNodes :: GraphInfo -- ^ The graph
          -> [NodeId] -- ^ IDs of the nodes to hide
          -> [(NodeId, NodeId, (DGEdgeType, Bool))] -- ^ A list of new edges
          -> IO ()
hideNodes gi nIds compedges = do
  threadDelay 300000
  showAll gi
  hideEdgesOfNodes gi nIds
  mapM_ (hideNode gi) nIds
  mapM_ (addCompressedEdge gi) compedges

-- | Checks whether a node is hidden or not
isHiddenNode :: GraphInfo -- ^ The graph
             -> NodeId -- ^ ID of the node
             -> IO Bool
isHiddenNode gi nId =
  fmap (isNothing . udgNode . get nId . nodes) $ readIORef gi

-- | Checks if at least one hidden node exists
hasHiddenNodes :: GraphInfo -- ^ The graph
               -> IO Bool
hasHiddenNodes =
  fmap (Map.fold (\ n b -> b || isNothing (udgNode n)) False . nodes)
    . readIORef

-- | Shows a hidden node again
showNode :: GraphInfo -- ^ The graph
         -> NodeId -- ^ ID of the node
         -> IO ()
showNode gi nId = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case udgNode node of
    Just _ -> return ()
    Nothing -> do
      node' <- newNode (theGraph g)
                       (udgNodeType $ get (ganType node) $ nodeTypes g)
                       $ ganValue node
      writeIORef gi g
       { nodes = Map.insert nId node { udgNode = Just node' } $ nodes g }

-- | Change the node type of the given node
changeNodeType :: GraphInfo -- ^ The graph
               -> NodeId -- ^ ID of the node
               -> DGNodeType -- ^ ID of the nodetype
               -> IO ()
changeNodeType gi nId nType = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case udgNode node of
        Nothing -> return ()
        Just node' -> setNodeType (theGraph g) node'
          $ udgNodeType $ get nType $ nodeTypes g
  writeIORef gi g
        { nodes = Map.insert nId node { ganType = nType } $ nodes g }

-- | Focus a node
focusNode :: GraphInfo -- ^ The graph
          -> NodeId -- ^ ID of the node
          -> IO ()
focusNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Nothing -> error "focusNode: node is hidden!"
    Just node -> setNodeFocus (theGraph g) node

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: GraphInfo -- ^ The graph
        -> EdgeId -- ^ ID of the edge
        -> DGEdgeType -- ^ ID of the edgetype
        -> NodeId -- ^ ID of source node
        -> NodeId -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> IO ()
addEdge gi eId eType nIdFrom nIdTo eName eLabel = do
  g' <- readIORef gi
  g <- if Map.member eId $ edges g' then do
      delEdge gi eId
      readIORef gi
    else return g'
  let gaeV = (eName, eId, eLabel)
  edge' <- case getEdgeAux g nIdFrom nIdTo eType (not . gaeHidden) of
      Just (nFrom, nTo, gaeT) ->
          fmap Just $ newArc (theGraph g) (udgEdgeType gaeT) gaeV nFrom nTo
      Nothing -> return Nothing
  let edge = GAEdge { udgEdge = edge'
                    , gaeType = eType
                    , ganFrom = nIdFrom
                    , ganTo = nIdTo
                    , gaeValue = gaeV }
  writeIORef gi g { edges = Map.insert eId edge $ edges g }

getEdgeAux :: AbstractionGraph -> NodeId -> NodeId -> DGEdgeType
  -> (GAEdgeType -> Bool)
  -> Maybe (DaVinciNode NodeValue, DaVinciNode NodeValue, GAEdgeType)
getEdgeAux g nIdFrom nIdTo eType f =
  let ns = nodes g
      gaeT = get eType $ edgeTypes g
  in case (udgNode $ get nIdFrom ns, udgNode $ get nIdTo ns) of
    (Just nFrom, Just nTo) | f gaeT -> Just (nFrom, nTo, gaeT)
    _ -> Nothing

-- | Adds an compressed edge
addCompressedEdge :: GraphInfo -- ^ The graph
                  -> (NodeId, NodeId, (DGEdgeType, Bool)) -- ^ src,tar,(et,orig)
                  -> IO ()
addCompressedEdge gi (nIdFrom, nIdTo, (eType, orig)) = do
  g <- readIORef gi
  let gaeV = ("", EdgeId 0, Nothing)
  edge' <- case getEdgeAux g nIdFrom nIdTo eType (not . gaeHidden) of
    Just (nFrom, nTo, gaeT) ->
      fmap Just $ newArc (theGraph g)
                         ((if orig then fst else snd) $ udgCompressed gaeT)
                         gaeV nFrom nTo
    Nothing -> return Nothing
  let edge = GAEdge { udgEdge = edge'
                    , gaeType = eType
                    , ganFrom = nIdFrom
                    , ganTo = nIdTo
                    , gaeValue = gaeV }
  writeIORef gi g { compressedEdges = edge : compressedEdges g }

-- | Deletes an edge
delEdge :: GraphInfo -- ^ The graph
        -> EdgeId -- ^ ID of the node
        -> IO ()
delEdge gi eId = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  writeIORef gi g { edges = Map.delete eId $ edges g }

-- | Deletes an compressed edge
delCompressedEdge :: GraphInfo -- ^ The graph
                  -> GAEdge -- ^ The compressed edge
                  -> IO ()
delCompressedEdge gi e = do
  g <- readIORef gi
  case udgEdge e of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()

-- | Hides an edge
hideEdge :: GraphInfo -- ^ The graph
         -> EdgeId -- ^ ID of the edge
         -> IO ()
hideEdge gi eId = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case udgEdge edge of
    Nothing -> return ()
    Just edge' -> do
      deleteArc (theGraph g) edge'
      writeIORef gi g
        { edges = Map.insert eId edge { udgEdge = Nothing } $ edges g }

-- | Hides incoming and outgoing edges of nodes
hideEdgesOfNodes :: GraphInfo -- ^ The graph
                 -> [NodeId] -- ^ IDs of the nodes to hide
                 -> IO ()
hideEdgesOfNodes gi nIds = do
  g <- readIORef gi
  mapM_ (hideEdge gi) $ map fst
        $ filter (\ (_,e) -> elem (ganTo e) nIds || elem (ganFrom e) nIds)
        $ Map.toList $ edges g

-- | Hides a set of edgetypes (type ids)
hideSetOfEdgeTypes :: GraphInfo -- ^ The graph
                   -> [DGEdgeType] -- ^ IDs of the edgetypes to hide
                   -> IO ()
hideSetOfEdgeTypes gi eTypes = do
  g <- readIORef gi
  let (hEdges, sEdges) = Map.foldWithKey (\ eid e (he, se) ->
         if elem (gaeType e) eTypes then (eid : he, se) else (he, eid : se))
         ([], []) $ edges g
  writeIORef gi g { edgeTypes = Map.mapWithKey
      (\ etId et -> et { gaeHidden = elem etId eTypes }) $ edgeTypes g }
  mapM_ (hideEdge gi) hEdges
  mapM_ (showEdge gi) sEdges

-- | Checks whether an edge is hidden or not
isHiddenEdge :: GraphInfo -- ^ The graph
             -> EdgeId -- ^ ID of the edge
             -> IO Bool
isHiddenEdge gi eId =
  fmap (isNothing . udgEdge . get eId . edges) $ readIORef gi

-- | Checks if at least one hiddes edge exists
hasHiddenEdges :: GraphInfo -- ^ The graph
               -> IO Bool
hasHiddenEdges =
  fmap (Map.fold (\ e b -> b || isNothing (udgEdge e)) False . edges)
    . readIORef

-- | Shows a hidden edge again
showEdge :: GraphInfo -- ^ The graph
         -> EdgeId -- ^ ID of the edge
         -> IO ()
showEdge gi eId = do
  g <- readIORef gi
  let es = edges g
      edge = get eId es
  case udgEdge edge of
    Just _ -> return ()
    Nothing -> case getEdgeAux g (ganFrom edge) (ganTo edge) (gaeType edge)
                (const True) of
      Just (nFrom, nTo, gaeT) -> do
          edge' <- newArc (theGraph g) (udgEdgeType gaeT) (gaeValue edge)
            nFrom nTo
          writeIORef gi g
            { edges = Map.insert eId edge { udgEdge = Just edge' } es }
      Nothing -> return ()

-- | Change the edge type of the given edge
changeEdgeType :: GraphInfo -- ^ The graph
               -> EdgeId -- ^ ID of the edge
               -> DGEdgeType -- ^ ID of the edgetype
               -> IO ()
changeEdgeType gi eId eType = do
  g <- readIORef gi
  let es = edges g
      edge = get eId es
  unless (eType == gaeType edge) $ case udgEdge edge of
      Nothing -> writeIORef gi g
        { edges = Map.insert eId edge { gaeType = eType } es }
      Just edge' ->
        case getEdgeAux g (ganFrom edge) (ganTo edge) eType (const True) of
          Just (nFrom, nTo, gaeT) -> do
            deleteArc (theGraph g) edge'
            e <- newArc (theGraph g) (udgEdgeType gaeT) (gaeValue edge)
                 nFrom nTo
            writeIORef gi g { edges = Map.insert eId edge
              { udgEdge = Just e
              , gaeType = eType } es }
          Nothing -> return () -- ignore error

-- * direct manipulation of uDrawGraph

-- | execute in the context of the given graph
doInGraphContext :: DVT.DaVinciCmd -> GraphInfo -> IO ()
doInGraphContext cmd gi = do
  g <- readIORef gi
  let Graph dg = theGraph g
  synchronize (pendingChangesLock dg) $ doInContext cmd
    $ getDaVinciGraphContext dg

-- | Improve the layout of a graph like calling \"Layout->Improve All\"
layoutImproveAll :: GraphInfo -- ^ The graph
                 -> IO ()
layoutImproveAll = doInGraphContext (DVT.Menu $ DVT.Layout $ DVT.ImproveAll)

-- | Display a message in a uDrawGraph window controlled by AbstractGraphView
showTemporaryMessage :: GraphInfo -- ^ The graph
                     -> String -- ^ message to be displayed
                     -> IO ()
showTemporaryMessage gi message =
  doInGraphContext (DVT.Window $ DVT.ShowMessage message) gi

-- | Deactivate the input of all uDrawGraph windows;
--
-- Warning: every deactivate event must be paired an activate event
deactivateGraphWindow :: GraphInfo -- ^ The graph
                      -> IO ()
deactivateGraphWindow = doInGraphContext (DVT.Window DVT.Deactivate)

-- | Activate the input of a uDrawGraph display
activateGraphWindow :: GraphInfo -- ^ The graph
                    -> IO ()
activateGraphWindow = doInGraphContext (DVT.Window DVT.Activate)

-- | Closes the Window
closeGraphWindow :: GraphInfo -- ^ The graph
                 -> IO ()
closeGraphWindow = doInGraphContext (DVT.Menu $ DVT.File DVT.Close)