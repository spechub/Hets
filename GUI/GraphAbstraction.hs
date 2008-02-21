{- |
Module      :  $Header$
Description :  Interface for graph viewing and abstraction
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (relies on Logic via DevGraph)

Interface for graph viewing and abstraction.
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
    -- * Types
    ( ID
    , NodeValue
    , EdgeValue
    , CompTable
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
    , hideSetOfNodeTypes'
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
type CompTable = [(String, String, String)]

data GANode = GANode -- ^ Internal node
  { udgNode :: Maybe (DaVinciNode NodeValue) -- ^ uDrawGraph node
  , ganType :: ID -- ^ ID of nodetype
  , ganValue :: NodeValue -- ^ Holds the nodevalue for uDrawGraph node
  }

data GAEdge = GAEdge -- ^ Internal edge
  { udgEdge :: Maybe (DaVinciArc EdgeValue) -- ^ uDrawGraph edge
  , ganFrom :: ID -- ^ ID of source node
  , ganTo :: ID -- ^ID of target node
  , gaeType :: ID -- ^ ID of edgetype
  , gaeValue :: EdgeValue -- ^ Holds the edgevalue for uDrawGraph edge
  }

data GANodeType = GANodeType
  { udgNodeType :: DaVinciNodeType NodeValue
  , ganHidden :: Bool
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
  , compTable :: Map.Map (ID, ID) ID
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
            , compTable = Map.empty
            }
  newIORef g

-- | Simpler version of makegraphExt
makegraph :: String        -- Title
          -> Maybe (IO ()) -- FileOpen Menu
          -> Maybe (IO ()) -- FileSave Menu
          -> Maybe (IO ()) -- FileSaveAs Menu
          -> [GlobalMenu]
          -> [(String,DaVinciNodeTypeParms NodeValue)]
          -> [(String,DaVinciArcTypeParms EdgeValue)]
          -> CompTable
          -> GraphInfo
          -> IO ()
makegraph title open save saveAs menus nodetypeparams edgetypeparams ct gi =
  makegraphExt title open save saveAs (return True) Nothing menus
               nodetypeparams edgetypeparams ct gi

-- | Creates the uDrawGraph graph
makegraphExt :: String     -- Title
          -> Maybe (IO ()) -- FileOpen Menu
          -> Maybe (IO ()) -- FileSave Menu
          -> Maybe (IO ()) -- FileSaveAs Menu
          -> IO Bool       -- FileClose Menu
          -> Maybe (IO ()) -- FileExit Menu
          -> [GlobalMenu]
          -> [(String,DaVinciNodeTypeParms NodeValue)]
          -> [(String,DaVinciArcTypeParms EdgeValue)]
          -> CompTable
          -> GraphInfo
          -> IO ()
makegraphExt title open save saveAs close exit menus nTypeParams eTypeParams ct
             gi = do
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
      eTypeParams2 =
        map (LocalMenu (Button "Expand" (\ _ -> hideSetOfNodeTypes [] gi)) $$$)
            eTypeParams1
  graph <- GraphDisp.newGraph graphtool graphParms
  nTypes <- mapM (newNodeType graph) nTypeParams1
  eTypes <- mapM (newArcType graph) eTypeParams1
  eTypes' <- mapM (newArcType graph) eTypeParams2
  let nTypeCount = length nTypeNames
      nTypeIds = enumFromTo 0 $ nTypeCount-1
      eTypeIds = enumFromTo nTypeCount $ length eTypeNames
      g = AbstractionGraph
            { theGraph = graph
            , nodes = IntMap.empty
            , edges = IntMap.empty
            , nodeTypes = IntMap.fromList $ zip nTypeIds $ map 
                (\nt -> GANodeType { udgNodeType = nt, ganHidden = False })
                nTypes
            , edgeTypes = IntMap.fromList $ zip eTypeIds $ map 
                (\(et, et') -> GAEdgeType { udgEdgeType = et
                                          , udgCompressed = et' 
                                          , gaeHidden = False })
                $ zip eTypes eTypes'
            , name2Id = Map.fromList $ zip (nTypeNames++eTypeNames)
                                           (nTypeIds++eTypeIds)
            , compTable = Map.empty
            }
  ct' <- mapM (\(t1, t2, t3) -> return $ ( ( get' t1 $ name2Id g
                                           , get' t2 $ name2Id g)
                                         , get' t3 $ name2Id g)) ct
  writeIORef gi $ g{ compTable = Map.fromList ct' }
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
showAll :: GraphInfo -> IO ()
showAll gi = do
  g <- readIORef gi
  nodes' <- filterM (\ nid -> isHiddenNode nid gi) $ IntMap.keys $ nodes g
  edges' <- filterM (\ eid -> isHiddenEdge eid gi) $ IntMap.keys $ edges g
  showNodes nodes' gi
  showEdges edges' gi

{- Functions for adding, deleting, changing and hidding nodes.-}

-- | Adds a node (type id)
addNode :: ID -- ^ ID of the node
        -> ID -- ^ ID of the nodetype
        -> String -- ^ Name of the node
        -> GraphInfo -> IO ()
addNode nId nType nName gi = do
  g' <- readIORef gi
  g <- case IntMap.member nId $ edges g' of
    True -> do
      delNode nId gi
      readIORef gi
    False -> return g'
  node' <- case ganHidden $ get nType $ nodeTypes g of
    True -> return Nothing
    False -> do
      n <- newNode (theGraph g) (udgNodeType $ get nType $ nodeTypes g)
                   (nName,nId)
      return $ Just n
  let node = GANode { udgNode = node'
                    , ganType = nType
                    , ganValue = (nName, nId)
                    }
  writeIORef gi $ g{ nodes = IntMap.insert nId node $ nodes g }

-- | Adds a node (type name)
addNode' :: ID -- ^ ID of the node
         -> String -- ^ Name of the nodetype
         -> String -- ^ Name of the node
         -> GraphInfo -> IO ()
addNode' nId nTypeName nName gi = do
  g <- readIORef gi
  addNode nId (get' nTypeName $ name2Id g) nName gi

-- | Deletes a node
delNode :: ID -- ^ ID of the node
        -> GraphInfo -> IO ()
delNode nId gi = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Just node -> deleteNode (theGraph g) node
    Nothing -> return ()
  writeIORef gi $ g{ nodes = IntMap.delete nId $ nodes g }

-- Needs to be reimplemented
hideSetOfNodeTypes :: [ID] -- ^ IDs of the nodetypes to hide
                   -> GraphInfo -> IO ()
hideSetOfNodeTypes _ _ = do
  return ()

{-
-- | Hides a node
hideNode :: ID -- ^ ID of the node
         -> GraphInfo -> IO ()
hideNode nId gi = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case udgNode node of
    Nothing -> return ()
    Just node' -> do
      deleteNode (theGraph g) node'
      writeIORef gi $ g{ nodes = IntMap.insert nId (node{udgNode = Nothing})
                                               $ nodes g }

-- | Hides a set of nodes
hideNodes :: [ID] -- ^ IDs of the nodes to hide
          -> GraphInfo -> IO ()
hideNodes [] _ = return ()
hideNodes (nId:r) gi = do
  hideNode nId gi
  hideNodes r gi  

-- | Hides a set of nodetypes (type ids)
hideSetOfNodeTypes :: [ID] -- ^ IDs of the nodetypes to hide
                   -> GraphInfo -> IO ()
hideSetOfNodeTypes nTypes gi = do
  g <- readIORef gi
  let (hNodes, sNodes) = IntMap.foldWithKey (\nid n (hn, sn) -> 
                           if elem (ganType n) nTypes then (nid:hn,sn)
                              else (hn,nid:sn)) ([],[]) $ nodes g
  writeIORef gi $ g{ nodeTypes = IntMap.mapWithKey (\ntId nt ->
                           if elem ntId nTypes then nt{ ganHidden = True }
                              else nt{ ganHidden = False }) $ nodeTypes g }
  hideNodes hNodes gi
  showNodes sNodes gi-}

-- | Hides a set of nodetypes (types names)
hideSetOfNodeTypes' :: [String] -- ^ Names of the nodetypes to hide
                    -> GraphInfo -> IO ()
hideSetOfNodeTypes' nTypeNames gi = do
  g <- readIORef gi
  hideSetOfNodeTypes (map (\n -> get' n $ name2Id g) nTypeNames) gi

-- | Checks whether a node is hidden or not
isHiddenNode :: ID -- ^ ID of the node
             -> GraphInfo -> IO Bool
isHiddenNode nId gi = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
   Just _ -> return False
   Nothing -> return True

-- | Checks if at least one hidden node exists
hasHiddenNodes :: GraphInfo -> IO Bool
hasHiddenNodes gi = do
  g <- readIORef gi
  return $ IntMap.fold (\node b -> if b then b else udgNode node == Nothing)
                       False $ nodes g

-- | Shows a hidden node again
showNode :: ID -- ^ ID of the node
         -> GraphInfo -> IO ()
showNode nId gi = do
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

-- | Shows a set of hidden nodes again
showNodes :: [ID] -- ^ IDs of the nodes to show
          -> GraphInfo -> IO ()
showNodes [] _ = return ()
showNodes (nId:r) gi = do
  showNode nId gi
  showNodes r gi

-- | Change the node type of the given node
changeNodeType :: ID -- ^ ID of the node
               -> ID -- ^ ID of the nodetype
               -> GraphInfo -> IO ()
changeNodeType nId nType gi = do
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
changeNodeType' :: ID -- ^ ID of the node
                -> String -- ^ Name of the nodetype
                -> GraphInfo -> IO ()
changeNodeType' nId nTypeName gi = do
  g <- readIORef gi
  changeNodeType nId (get' nTypeName $ name2Id g) gi

-- | Focus a node
focusNode :: ID
          -> GraphInfo -> IO ()
focusNode nId gi = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Nothing -> error "focusNode: node is hidden!\n"
    Just node -> setNodeFocus (theGraph g) node

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: ID -- ^ ID of the edge
        -> ID -- ^ ID of the edgetype
        -> ID -- ^ ID of source node
        -> ID -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> GraphInfo -> IO ()
addEdge eId eType nIdFrom nIdTo eName eLabel gi = do
  g' <- readIORef gi
  g <- case IntMap.member eId $ edges g' of
    True -> do
      delEdge eId gi
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
addEdge' :: ID -- ^ ID of the edge
         -> String -- ^ Name of the edgetype
         -> ID -- ^ ID of source node
         -> ID -- ^ ID of target node
         -> String -- ^ Name of the edge
         -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
         -> GraphInfo -> IO ()
addEdge' eId eTypeName nIdFrom nIdTo eName eLable gi = do
  g <- readIORef gi
  addEdge eId (get' eTypeName $ name2Id g) nIdFrom nIdTo eName eLable gi

-- | Deletes an edge
delEdge :: ID -- ^ ID of the node
        -> GraphInfo -> IO ()
delEdge eId gi = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  writeIORef gi $ g{ edges = IntMap.delete eId $ edges g }

-- | Hides an edge
hideEdge :: ID -- ^ ID of the edge
         -> GraphInfo -> IO ()
hideEdge eId gi = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case udgEdge edge of
    Nothing -> return ()
    Just edge' -> do
      deleteArc (theGraph g) edge'
      writeIORef gi $ g{ edges = IntMap.insert eId (edge{ udgEdge = Nothing })
                                               $ edges g }

-- | Hides a set of edges
hideEdges :: [ID] -- ^ IDs of the edges to hide
          -> GraphInfo -> IO ()
hideEdges [] _ = return ()
hideEdges (eId:r) gi = do
  hideEdge eId gi
  hideEdges r gi

-- | Hides a set of edgetypes (type ids)
hideSetOfEdgeTypes :: [ID] -- ^ IDs of the edgetypes to hide
                   -> GraphInfo -> IO ()
hideSetOfEdgeTypes eTypes gi = do
  g <- readIORef gi
  let (hEdges, sEdges) = IntMap.foldWithKey (\eid e (he, se) ->
                           if elem (gaeType e) eTypes then (eid:he,se)
                              else (he,eid:se)) ([],[]) $ edges g
  writeIORef gi $ g{ edgeTypes = IntMap.mapWithKey (\etId et ->
                           if elem etId eTypes then et{ gaeHidden = True }
                              else et{ gaeHidden = False }) $ edgeTypes g}
  hideEdges hEdges gi
  showEdges sEdges gi

-- | Hides a set of edgetypes (type names)
hideSetOfEdgeTypes' :: [String] -- ^ Names of the edgetypes to hide
                    -> GraphInfo -> IO ()
hideSetOfEdgeTypes' eTypeNames gi = do
  g <- readIORef gi
  hideSetOfEdgeTypes (map (\n -> get' n $ name2Id g) eTypeNames) gi

-- | Checks whether an edge is hidden or not
isHiddenEdge :: ID -- ^ ID of the edge
             -> GraphInfo -> IO Bool
isHiddenEdge eId gi = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
   Just _ -> return False
   Nothing -> return True

-- | Checks if at least one hiddes edge exists
hasHiddenEdges :: GraphInfo -> IO Bool
hasHiddenEdges gi = do
  g <- readIORef gi
  return $ IntMap.fold (\edge b -> if b then b else udgEdge edge == Nothing)
                       False $ edges g

-- | Shows a hidden edge again
showEdge :: ID -- ^ ID of the edge
         -> GraphInfo -> IO ()
showEdge eId gi = do
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

-- | Shows a set of hidden edges again
showEdges :: [ID] -- ^ IDs of the edges to show
          -> GraphInfo -> IO ()
showEdges [] _ = return ()
showEdges (eId:r) gi = do
  showEdge eId gi
  showEdges r gi

-- | Change the edge type of the given edge
changeEdgeType :: ID -- ^ ID of the edge
               -> ID -- ^ ID of the edgetype
               -> GraphInfo -> IO ()
changeEdgeType eId eType gi = do
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
changeEdgeType' :: ID -- ^ ID of the edge
                -> String -- ^ Name of the edgetype
                -> GraphInfo -> IO ()
changeEdgeType' eId eTypeName gi = do
  g <- readIORef gi
  changeEdgeType eId (get' eTypeName $ name2Id g) gi

{- Direct manipulation of the uDrawGraph -}

-- | Improve the layout of a graph like calling \"Layout->Improve All\"
layoutImproveAll :: GraphInfo -> IO ()
layoutImproveAll gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Menu $ DVT.Layout $ DVT.ImproveAll) contxt
  return ()

-- | Display a message in a uDrawGraph window controlled by AbstractGraphView
showTemporaryMessage :: GraphInfo
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
deactivateGraphWindow :: GraphInfo -> IO ()
deactivateGraphWindow gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Window DVT.Deactivate) contxt
  return ()

-- | Activate the input of a uDrawGraph display
activateGraphWindow :: GraphInfo -> IO ()
activateGraphWindow gi = do
  g <- readIORef gi
  let contxt = case theGraph g of
                 Graph dg -> getDaVinciGraphContext dg
  doInContext (DVT.Window DVT.Activate) contxt
  return ()
