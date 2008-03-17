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
{-
   It is pos        (Button
           "Show number of node" (\ (_, descr, _) -> getNumberOfNode descr))

GUI/GraphMenu2.hs:534:54:
    Couldn't match expected type `DGraph' against inferred type `Int'
    Probable cause: `getNumberOsible to hide sets of nodes and edges.
   Using a composition table for edge types,
   paths through hidden nodes can be displayed.
   Graphs, nodes, and edges are handled via
   descriptors (here: integers), while node and
   edge types are handled by user-supplied strings.
-}

module GUI.GraphAbstraction
    ( -- * Types
      ID
    , NodeValue
    , EdgeValue
    , GraphInfo
    -- * Creation and display
    , initgraphs
    , makegraph
    , makegraphExt
    , redisplay
    , showAll
    -- * Node interface
    , addNode'
    , delNode
    , hideNodes'
    , isHiddenNode
    , hasHiddenNodes
    , changeNodeType'
    , focusNode
    -- * Edge interface
    , addEdge'
    , delEdge
    , hideSetOfEdgeTypes'
    , isHiddenEdge
    , hasHiddenEdges
    , changeEdgeType'
    -- * Direct manipulation of uDrawGraph
    , layoutImproveAll
    , showTemporaryMessage
    , deactivateGraphWindow
    , activateGraphWindow
    ) where

import DaVinciGraph
import DaVinciBasic
import qualified DaVinciTypes as DVT
import GraphDisp
import GraphConfigure

import ATC.DevGraph()
import Static.DevGraph (DGLinkLab)

import Data.IORef
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LEdge)
import qualified Data.Graph.Inductive.Graph as Graph

import Control.Concurrent
import Control.Monad (filterM)

type OurGraph =
     Graph   DaVinciGraph
             DaVinciGraphParms
             DaVinciNode
             DaVinciNodeType
             DaVinciNodeTypeParms
             DaVinciArc
             DaVinciArcType
             DaVinciArcTypeParms

type ID = IntMap.Key
type NodeValue = (String, ID)
type EdgeValue = (String, ID, Maybe (LEdge DGLinkLab))

-- | Internal node
data GANode = GANode
  { udgNode :: Maybe (DaVinciNode NodeValue) -- ^ uDrawGraph node
  , ganType :: ID -- ^ ID of nodetype
  , ganValue :: NodeValue -- ^ Holds the nodevalue for uDrawGraph node
  }

-- | Internal edge
data GAEdge = GAEdge
  { udgEdge :: Maybe (DaVinciArc EdgeValue) -- ^ uDrawGraph edge
  , ganFrom :: ID -- ^ ID of source node
  , ganTo :: ID -- ^ID of target node
  , gaeType :: ID -- ^ ID of edgetype
  , gaeValue :: EdgeValue -- ^ Holds the edgevalue for uDrawGraph edge
  }

data GANodeType = GANodeType
  { udgNodeType :: DaVinciNodeType NodeValue
  }

data GAEdgeType = GAEdgeType
  { udgEdgeType :: DaVinciArcType EdgeValue
  , udgCompressed :: DaVinciArcType EdgeValue
  , gaeHidden :: Bool
  }

-- Main datastructure for carrying around the graph,
-- both internally (nodes as integers), and at the daVinci level
data AbstractionGraph = AbstractionGraph
  { theGraph :: OurGraph
  , nodes :: IntMap.IntMap GANode
  , edges :: IntMap.IntMap GAEdge
  , nodeTypes :: IntMap.IntMap GANodeType
  , edgeTypes :: IntMap.IntMap GAEdgeType
  , name2Id :: Map.Map String ID
  , compressedEdges :: [GAEdge]
  }

type GraphInfo = IORef AbstractionGraph

instance Eq (DaVinciNode NodeValue) where
    (==) = eq1

instance Eq (DaVinciArc EdgeValue) where
    (==) = eq1

-- | Wait for this amount of microseconds to let uDrawGraph redraw
delayTime :: Int
delayTime = 300000

-- | Forces a redraw of the uDrawGraph and wait an amount of time
redisplay :: GraphInfo -> IO ()
redisplay gi = do
  threadDelay delayTime
  g <- readIORef gi
  redraw (theGraph g)

-- | Creates an empty graph structure
graphtool :: OurGraph
graphtool = daVinciSort

-- | Creates the empty AbstractionGraph
initgraphs :: IO GraphInfo
initgraphs = do
  let g = AbstractionGraph
            { theGraph = graphtool
            , nodes = IntMap.empty
            , edges = IntMap.empty
            , nodeTypes = IntMap.empty
            , edgeTypes = IntMap.empty
            , name2Id = Map.empty
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
          -> [(String,DaVinciNodeTypeParms NodeValue)]
          -> [(String,DaVinciArcTypeParms EdgeValue)]
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
             -> [(String,DaVinciNodeTypeParms NodeValue)]
             -> [(String,DaVinciArcTypeParms EdgeValue)]
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
      (nTypeNames,nTypeParams1) = unzip nTypeParams
      (eTypeNames,eTypeParams1) = unzip eTypeParams
      eTypeParams2 = map (LocalMenu (Button "Expand" (\ _ -> do
                                                       showAll gi
                                                       redisplay gi)) $$$)
                         eTypeParams1
  graph <- GraphDisp.newGraph graphtool graphParms
  nTypes <- mapM (newNodeType graph) nTypeParams1
  eTypes <- mapM (newArcType graph) eTypeParams1
  eTypes' <- mapM (newArcType graph) eTypeParams2
  let nTypeCount = length nTypeNames
      nTypeIds = enumFromTo 0 $ nTypeCount - 1
      eTypeIds = enumFromTo nTypeCount $ nTypeCount - 1 + length eTypeNames
      g = AbstractionGraph
            { theGraph = graph
            , nodes = IntMap.empty
            , edges = IntMap.empty
            , nodeTypes = IntMap.fromList $ zip nTypeIds $ map
                (\nt -> GANodeType { udgNodeType = nt })
                nTypes
            , edgeTypes = IntMap.fromList $ zip eTypeIds $ map
                (\(et, et') -> GAEdgeType { udgEdgeType = et
                                          , udgCompressed = et'
                                          , gaeHidden = False })
                $ zip eTypes eTypes'
            , name2Id = Map.fromList $ zip (nTypeNames++eTypeNames)
                                           (nTypeIds++eTypeIds)
            , compressedEdges = []
            }
  writeIORef gi g
  return ()

{- similar to lookup (for IntMap), but returns just the value if lookup was
   successful otherwise an error is raised. -}
get :: ID -> IntMap.IntMap a -> a
get key imap =
  case IntMap.lookup key imap of
    Just r -> r
    Nothing -> error $ "get: id unknown: " ++ (show key) ++ "\n"

{- similar to lookup (for Map), but returns just the value if lookup was
   successful otherwise an error is raised. -}
get' :: String -> Map.Map String a -> a
get' key m =
  case Map.lookup key m of
    Just r -> r
    Nothing -> error $ "get': id unknown: " ++ key ++ "\n"

-- | Shows all hidden nodes and edges
showAll :: GraphInfo -- ^ The graph
        -> IO ()
showAll gi = do
  g <- readIORef gi
  mapM_ (delCompressedEdge gi) $ compressedEdges g
  nodes' <- filterM (isHiddenNode gi) $ IntMap.keys $ nodes g
  edges' <- filterM (isHiddenEdge gi) $ IntMap.keys $ edges g
  writeIORef gi $ g{ compressedEdges = [] }
  mapM_ (showNode gi) nodes'
  mapM_ (showEdge gi) edges'

{- Functions for adding, deleting, changing and hidding nodes.-}

-- | Adds a node (type id)
addNode :: GraphInfo -- ^ The graph
        -> ID -- ^ ID of the node
        -> ID -- ^ ID of the nodetype
        -> String -- ^ Name of the node
        -> IO ()
addNode gi nId nType nName = do
  g' <- readIORef gi
  g <- case IntMap.member nId $ nodes g' of
    True -> do
      delNode gi nId
      readIORef gi
    False -> return g'
  node' <- newNode (theGraph g) (udgNodeType $ get nType $ nodeTypes g)
                   (nName,nId)
  let node = GANode { udgNode = Just node'
                    , ganType = nType
                    , ganValue = (nName, nId)
                    }
  writeIORef gi $ g{ nodes = IntMap.insert nId node $ nodes g }

-- | Adds a node (type name)
addNode' :: GraphInfo -- ^ The graph
         -> ID -- ^ ID of the node
         -> String -- ^ Name of the nodetype
         -> String -- ^ Name of the node
         -> IO ()
addNode' gi nId nTypeName nName = do
  g <- readIORef gi
  addNode gi nId (get' nTypeName $ name2Id g) nName

-- | Deletes a node
delNode :: GraphInfo -- ^ The graph
        -> ID -- ^ ID of the node
        -> IO ()
delNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Just node -> deleteNode (theGraph g) node
    Nothing -> return ()
  writeIORef gi $ g{ nodes = IntMap.delete nId $ nodes g }

-- | Hides a node
hideNode :: GraphInfo -- ^ The graph
         -> ID -- ^ ID of the node
         -> IO ()
hideNode gi nId = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case udgNode node of
    Nothing -> return ()
    Just node' -> do
      deleteNode (theGraph g) node'
      writeIORef gi $ g{ nodes = IntMap.insert nId (node{udgNode = Nothing})
                                               $ nodes g }

-- | Hides a set of nodes
hideNodes :: GraphInfo -- ^ The graph
          -> [ID] -- ^ IDs of the nodes to hide
          -> [(ID,ID,ID)] -- ^ A list of new edges
          -> IO ()
hideNodes gi nIds compedges = do
  showAll gi
  hideEdgesOfNodes gi nIds
  mapM_ (hideNode gi) nIds
  mapM_ (addCompressedEdge gi) compedges

-- | Hides a set of nodes
hideNodes' :: GraphInfo -- ^ The graph
           -> [ID] -- ^ IDs of the nodes to hide
           -> [(ID,ID,String)] -- ^ A list of new edges
           -> IO ()
hideNodes' gi nIds compedges = do
  g <- readIORef gi
  hideNodes gi nIds (map (\(s,t,et) -> (s,t,get' et $ name2Id g)) compedges)

-- | Checks whether a node is hidden or not
isHiddenNode :: GraphInfo -- ^ The graph
             -> ID -- ^ ID of the node
             -> IO Bool
isHiddenNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
   Just _ -> return False
   Nothing -> return True

-- | Checks if at least one hidden node exists
hasHiddenNodes :: GraphInfo -- ^ The graph
               -> IO Bool
hasHiddenNodes gi = do
  g <- readIORef gi
  return $ IntMap.fold (\node b -> if b then b else udgNode node == Nothing)
                       False $ nodes g

-- | Shows a hidden node again
showNode :: GraphInfo -- ^ The graph
         -> ID -- ^ ID of the node
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
      writeIORef gi $ g{ nodes = IntMap.insert nId (node{udgNode = Just node'})
                                               $ nodes g }

-- | Change the node type of the given node
changeNodeType :: GraphInfo -- ^ The graph
               -> ID -- ^ ID of the node
               -> ID -- ^ ID of the nodetype
               -> IO ()
changeNodeType gi nId nType = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case IntMap.lookup nType $ nodeTypes g of
    Nothing -> error $ "changeNodeType: unknown NodeType: "++(show nType)++"\n"
    Just nType' -> do
      case udgNode node of
        Nothing -> return ()
        Just node' -> setNodeType (theGraph g) node' $ udgNodeType nType'
      writeIORef gi $ g{ nodes = IntMap.insert nId (node{ ganType = nType })
                                               $ nodes g }

-- | Change the node type of the given node
changeNodeType' :: GraphInfo -- ^ The graph
                -> ID -- ^ ID of the node
                -> String -- ^ Name of the nodetype
                -> IO ()
changeNodeType' gi nId nTypeName = do
  g <- readIORef gi
  changeNodeType gi nId (get' nTypeName $ name2Id g)

-- | Focus a node
focusNode :: GraphInfo -- ^ The graph
          -> ID
          -> IO ()
focusNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Nothing -> error "focusNode: node is hidden!\n"
    Just node -> setNodeFocus (theGraph g) node

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: GraphInfo -- ^ The graph
        -> ID -- ^ ID of the edge
        -> ID -- ^ ID of the edgetype
        -> ID -- ^ ID of source node
        -> ID -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> IO ()
addEdge gi eId eType nIdFrom nIdTo eName eLabel = do
  g' <- readIORef gi
  g <- case IntMap.member eId $ edges g' of
    True -> do
      delEdge gi eId
      readIORef gi
    False -> return g'
  let nFrom = get nIdFrom $ nodes g
      nTo = get nIdTo $ nodes g
  edge' <- case gaeHidden $ get eType $ edgeTypes g of
    True -> return Nothing
    False -> case udgNode nFrom of
      Nothing -> return Nothing
      Just nFrom' -> case udgNode nTo of
        Nothing -> return Nothing
        Just nTo' -> do
          e <- newArc (theGraph g) (udgEdgeType $ get eType $ edgeTypes g)
                      (eName,eId,eLabel) (nFrom') (nTo')
          return $ Just e
  let edge = GAEdge { udgEdge = edge'
                    , gaeType = eType
                    , ganFrom = nIdFrom
                    , ganTo = nIdTo
                    , gaeValue = (eName, eId, eLabel)
                    }
  writeIORef gi $ g{ edges = IntMap.insert eId edge $ edges g }

-- | Adds an edge (type name)
addEdge' :: GraphInfo -- ^ The graph
         -> ID -- ^ ID of the edge
         -> String -- ^ Name of the edgetype
         -> ID -- ^ ID of source node
         -> ID -- ^ ID of target node
         -> String -- ^ Name of the edge
         -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
         -> IO ()
addEdge' gi eId eTypeName nIdFrom nIdTo eName eLable = do
  g <- readIORef gi
  addEdge gi eId (get' eTypeName $ name2Id g) nIdFrom nIdTo eName eLable

-- | Adds an compressed edge
addCompressedEdge :: GraphInfo -- ^ The graph
                  -> (ID,ID,ID) -- ^ ID of source, target and edgetype
                  -> IO ()
addCompressedEdge gi (nIdFrom,nIdTo,eType) = do
  g <- readIORef gi
  let nFrom = get nIdFrom $ nodes g
      nTo = get nIdTo $ nodes g
  edge' <- case gaeHidden $ get eType $ edgeTypes g of
    True -> return Nothing
    False -> case udgNode nFrom of
      Nothing -> return Nothing
      Just nFrom' -> case udgNode nTo of
        Nothing -> return Nothing
        Just nTo' -> do
          e <- newArc (theGraph g) (udgCompressed $ get eType $ edgeTypes g)
                      ("",0,Nothing) (nFrom') (nTo')
          return $ Just e
  let edge = GAEdge { udgEdge = edge'
                    , gaeType = eType
                    , ganFrom = nIdFrom
                    , ganTo = nIdTo
                    , gaeValue = ("",0,Nothing)
                    }
  writeIORef gi $ g{ compressedEdges = edge:compressedEdges g }

-- | Deletes an edge
delEdge :: GraphInfo -- ^ The graph
        -> ID -- ^ ID of the node
        -> IO ()
delEdge gi eId = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  writeIORef gi $ g{ edges = IntMap.delete eId $ edges g }

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
         -> ID -- ^ ID of the edge
         -> IO ()
hideEdge gi eId = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case udgEdge edge of
    Nothing -> return ()
    Just edge' -> do
      deleteArc (theGraph g) edge'
      writeIORef gi $ g{ edges = IntMap.insert eId (edge{ udgEdge = Nothing })
                                               $ edges g }

-- | Hides incoming and outgoing edges of nodes
hideEdgesOfNodes :: GraphInfo -- ^ The graph
                 -> [ID] -- ^ IDs of the nodes to hide
                 -> IO ()
hideEdgesOfNodes gi nIds = do
  g <- readIORef gi
  mapM_ (hideEdge gi) $ map fst
        $ filter (\ (_,e) -> elem (ganTo e) nIds || elem (ganFrom e) nIds)
        $ IntMap.toList $ edges g

-- | Hides a set of edgetypes (type ids)
hideSetOfEdgeTypes :: GraphInfo -- ^ The graph
                   -> [ID] -- ^ IDs of the edgetypes to hide
                   -> IO ()
hideSetOfEdgeTypes gi eTypes = do
  g <- readIORef gi
  let (hEdges, sEdges) = IntMap.foldWithKey (\eid e (he, se) ->
                           if elem (gaeType e) eTypes then (eid:he,se)
                              else (he,eid:se)) ([],[]) $ edges g
  writeIORef gi $ g{ edgeTypes = IntMap.mapWithKey (\etId et ->
                           if elem etId eTypes then et{ gaeHidden = True }
                              else et{ gaeHidden = False }) $ edgeTypes g}
  mapM_ (hideEdge gi) hEdges
  mapM_ (showEdge gi) sEdges

-- | Hides a set of edgetypes (type names)
hideSetOfEdgeTypes' :: GraphInfo -- ^ The graph
                    -> [String] -- ^ Names of the edgetypes to hide
                    -> IO ()
hideSetOfEdgeTypes' gi eTypeNames = do
  g <- readIORef gi
  hideSetOfEdgeTypes gi (map (\n -> get' n $ name2Id g) eTypeNames)

-- | Checks whether an edge is hidden or not
isHiddenEdge :: GraphInfo -- ^ The graph
             -> ID -- ^ ID of the edge
             -> IO Bool
isHiddenEdge gi eId = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
   Just _ -> return False
   Nothing -> return True

-- | Checks if at least one hiddes edge exists
hasHiddenEdges :: GraphInfo -- ^ The graph
               -> IO Bool
hasHiddenEdges gi = do
  g <- readIORef gi
  return $ IntMap.fold (\edge b -> if b then b else udgEdge edge == Nothing)
                       False $ edges g

-- | Shows a hidden edge again
showEdge :: GraphInfo -- ^ The graph
         -> ID -- ^ ID of the edge
         -> IO ()
showEdge gi eId = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case udgEdge edge of
    Just _ -> return ()
    Nothing -> case udgNode $ get (ganFrom edge) $ nodes g of
      Nothing -> return ()
      Just nFrom' -> case udgNode $ get (ganTo edge) $ nodes g of
        Nothing -> return ()
        Just nTo' -> do
          edge' <- newArc (theGraph g)
                          (udgEdgeType $ get (gaeType edge) $ edgeTypes g)
                          (gaeValue edge) (nFrom') (nTo')
          writeIORef gi $ g{ edges = IntMap.insert eId
                                                   (edge{ udgEdge = Just edge'})
                                                   $ edges g }

-- | Change the edge type of the given edge
changeEdgeType :: GraphInfo -- ^ The graph
               -> ID -- ^ ID of the edge
               -> ID -- ^ ID of the edgetype
               -> IO ()
changeEdgeType gi eId eType = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case eType == (gaeType $ edge) of
    True -> return ()
    False -> do
      case IntMap.lookup eType $ edgeTypes g of
        Nothing -> error $ "changeEdgeType: unknown EdgeType: " ++ (show eType)
        Just eType' -> do
          case udgEdge edge of
            Nothing -> writeIORef gi $ g{ edges = IntMap.insert eId
                                         (edge{ gaeType = eType }) $ edges g }
            Just edge' -> do
              deleteArc (theGraph g) edge'
              let Just from = udgNode $ get (ganFrom edge) $ nodes g
                  Just to = udgNode $ get (ganTo edge) $ nodes g
              e <- newArc (theGraph g) (udgEdgeType $ eType') (gaeValue edge)
                          from to
              writeIORef gi $ g{ edges = IntMap.insert eId
                                                       (edge{ udgEdge = Just e
                                                            , gaeType = eType })
                                                       $ edges g }

-- | Change the edge type of the given edge
changeEdgeType' :: GraphInfo -- ^ The graph
                -> ID -- ^ ID of the edge
                -> String -- ^ Name of the edgetype
                -> IO ()
changeEdgeType' gi eId eTypeName = do
  g <- readIORef gi
  changeEdgeType gi eId (get' eTypeName $ name2Id g)

{- Direct manipulation of the uDrawGraph -}

-- | Improve the layout of a graph like calling \"Layout->Improve All\"
layoutImproveAll :: GraphInfo -- ^ The graph
                 -> IO ()
layoutImproveAll gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Menu $ DVT.Layout $ DVT.ImproveAll) contxt
  return ()

-- | Display a message in a uDrawGraph window controlled by AbstractGraphView
showTemporaryMessage :: GraphInfo -- ^ The graph
                     -> String -- ^ message to be displayed
                     -> IO ()
showTemporaryMessage gi message = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Window $ DVT.ShowMessage message) contxt
  return ()

-- | Deactivate the input of all uDrawGraph windows;
--
-- Warning: every deactivate event must be paired an activate event
deactivateGraphWindow :: GraphInfo -- ^ The graph
                      -> IO ()
deactivateGraphWindow gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Window DVT.Deactivate) contxt
  return ()

-- | Activate the input of a uDrawGraph display
activateGraphWindow :: GraphInfo -- ^ The graph
                    -> IO ()
activateGraphWindow gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Window DVT.Activate) contxt
  return ()
