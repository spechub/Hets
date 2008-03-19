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
import Static.DevGraph (DGLinkLab, EdgeId(..))

import Data.IORef
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

type NodeId = Int

type NodeValue = (String, NodeId)
type EdgeValue = (String, EdgeId, Maybe (LEdge DGLinkLab))

newtype NodeTypeId = NodeTypeId Int deriving (Show, Eq, Ord, Enum)
newtype EdgeTypeId = EdgeTypeId Int deriving (Show, Eq, Ord, Enum)

-- | Internal node
data GANode = GANode
  { udgNode :: Maybe (DaVinciNode NodeValue) -- ^ uDrawGraph node
  , ganType :: NodeTypeId -- ^ ID of nodetype
  , ganValue :: NodeValue -- ^ Holds the nodevalue for uDrawGraph node
  }

-- | Internal edge
data GAEdge = GAEdge
  { udgEdge :: Maybe (DaVinciArc EdgeValue) -- ^ uDrawGraph edge
  , ganFrom :: NodeId -- ^ ID of source node
  , ganTo :: NodeId -- ^ID of target node
  , gaeType :: EdgeTypeId -- ^ ID of edgetype
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
  , nodes :: Map.Map NodeId GANode
  , edges :: Map.Map EdgeId GAEdge
  , nodeTypes :: Map.Map NodeTypeId GANodeType
  , edgeTypes :: Map.Map EdgeTypeId GAEdgeType
  , nodeType2Id :: Map.Map String NodeTypeId
  , edgeType2Id :: Map.Map String EdgeTypeId
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
            , nodes = Map.empty
            , edges = Map.empty
            , nodeTypes = Map.empty
            , edgeTypes = Map.empty
            , nodeType2Id = Map.empty
            , edgeType2Id = Map.empty
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
  let (nTypeNames', nodeTypes') = zipNodeTypes nTypeNames nTypes 0
      (eTypeNames', edgeTypes') = zipEdgeTypes eTypeNames (zip eTypes eTypes') 0
      g = AbstractionGraph
            { theGraph = graph
            , nodes = Map.empty
            , edges = Map.empty
            , nodeTypes = Map.fromList nodeTypes'
            , edgeTypes = Map.fromList edgeTypes'
            , nodeType2Id = Map.fromList nTypeNames'
            , edgeType2Id = Map.fromList eTypeNames'
            , compressedEdges = []
            }
  writeIORef gi g
  return ()

-- | Creates to each node type a id and the GANodeType
zipNodeTypes :: [String]
             -> [(DaVinciNodeType NodeValue)]
             -> Int
             -> ([(String, NodeTypeId)], [(NodeTypeId, GANodeType)])            
zipNodeTypes [] _ _ = ([],[])
zipNodeTypes _ [] _ = ([],[])
zipNodeTypes (name:rn) (nType:rt) i = ((name,ntId):n, (ntId, nt):t)
  where
    (n, t) = zipNodeTypes rn rt $ i+1
    ntId = NodeTypeId i
    nt = GANodeType { udgNodeType = nType }

-- | Creates to each edge type a id and the GAEdgeType
zipEdgeTypes :: [String]
             -> [(DaVinciArcType EdgeValue, DaVinciArcType EdgeValue)]
             -> Int
             -> ([(String, EdgeTypeId)], [(EdgeTypeId, GAEdgeType)])
zipEdgeTypes [] _ _ = ([],[])
zipEdgeTypes _ [] _ = ([],[])
zipEdgeTypes (name:rn) ((eType, cType):rt) i = ((name,etId):n, (etId, et):t)
  where
    (n, t) = zipEdgeTypes rn rt $ i+1
    etId = EdgeTypeId i
    et = GAEdgeType { udgEdgeType = eType
                    , udgCompressed = cType
                    , gaeHidden = False }

{- similar to lookup (for Map), but returns just the value if lookup was
   successful otherwise an error is raised. -}
get :: (Show k, Ord k) => k -> Map.Map k a -> a
get key map' =
  case Map.lookup key map' of
    Just r -> r
    Nothing -> error $ "get: id unknown: " ++ (show key) ++ "\n"

-- | Shows all hidden nodes and edges
showAll :: GraphInfo -- ^ The graph
        -> IO ()
showAll gi = do
  g <- readIORef gi
  mapM_ (delCompressedEdge gi) $ compressedEdges g
  nodes' <- filterM (isHiddenNode gi) $ Map.keys $ nodes g
  edges' <- filterM (isHiddenEdge gi) $ Map.keys $ edges g
  writeIORef gi $ g{ compressedEdges = [] }
  mapM_ (showNode gi) nodes'
  mapM_ (showEdge gi) edges'

{- Functions for adding, deleting, changing and hidding nodes.-}

-- | Adds a node (type id)
addNode :: GraphInfo -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> NodeTypeId -- ^ ID of the nodetype
        -> String -- ^ Name of the node
        -> IO ()
addNode gi nId nType nName = do
  g' <- readIORef gi
  g <- case Map.member nId $ nodes g' of
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
  writeIORef gi $ g{ nodes = Map.insert nId node $ nodes g }

-- | Adds a node (type name)
addNode' :: GraphInfo -- ^ The graph
         -> NodeId -- ^ ID of the node
         -> String -- ^ Name of the nodetype
         -> String -- ^ Name of the node
         -> IO ()
addNode' gi nId nTypeName nName = do
  g <- readIORef gi
  addNode gi nId (get nTypeName $ nodeType2Id g) nName

-- | Deletes a node
delNode :: GraphInfo -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> IO ()
delNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Just node -> deleteNode (theGraph g) node
    Nothing -> return ()
  writeIORef gi $ g{ nodes = Map.delete nId $ nodes g }

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
      writeIORef gi $ g{ nodes = Map.insert nId (node{udgNode = Nothing})
                                            $ nodes g }

-- | Hides a set of nodes
hideNodes :: GraphInfo -- ^ The graph
          -> [NodeId] -- ^ IDs of the nodes to hide
          -> [(NodeId, NodeId, EdgeTypeId)] -- ^ A list of new edges
          -> IO ()
hideNodes gi nIds compedges = do
  showAll gi
  hideEdgesOfNodes gi nIds
  mapM_ (hideNode gi) nIds
  mapM_ (addCompressedEdge gi) compedges

-- | Hides a set of nodes
hideNodes' :: GraphInfo -- ^ The graph
           -> [NodeId] -- ^ IDs of the nodes to hide
           -> [(NodeId, NodeId, String)] -- ^ A list of new edges
           -> IO ()
hideNodes' gi nIds compedges = do
  g <- readIORef gi
  hideNodes gi nIds (map (\(s,t,et) -> (s,t,get et $ edgeType2Id g)) compedges)

-- | Checks whether a node is hidden or not
isHiddenNode :: GraphInfo -- ^ The graph
             -> NodeId -- ^ ID of the node
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
  return $ Map.fold (\node b -> if b then b else udgNode node == Nothing) False
                    $ nodes g

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
      writeIORef gi $ g{ nodes = Map.insert nId (node{udgNode = Just node'})
                                            $ nodes g }

-- | Change the node type of the given node
changeNodeType :: GraphInfo -- ^ The graph
               -> NodeId -- ^ ID of the node
               -> NodeTypeId -- ^ ID of the nodetype
               -> IO ()
changeNodeType gi nId nType = do
  g <- readIORef gi
  let node = get nId $ nodes g
  case Map.lookup nType $ nodeTypes g of
    Nothing -> error $ "changeNodeType: unknown NodeType: "++(show nType)++"\n"
    Just nType' -> do
      case udgNode node of
        Nothing -> return ()
        Just node' -> setNodeType (theGraph g) node' $ udgNodeType nType'
      writeIORef gi $ g{ nodes = Map.insert nId (node{ ganType = nType })
                                            $ nodes g }

-- | Change the node type of the given node
changeNodeType' :: GraphInfo -- ^ The graph
                -> NodeId -- ^ ID of the node
                -> String -- ^ Name of the nodetype
                -> IO ()
changeNodeType' gi nId nTypeName = do
  g <- readIORef gi
  changeNodeType gi nId (get nTypeName $ nodeType2Id g)

-- | Focus a node
focusNode :: GraphInfo -- ^ The graph
          -> NodeId -- ^ ID of the node
          -> IO ()
focusNode gi nId = do
  g <- readIORef gi
  case udgNode $ get nId $ nodes g of
    Nothing -> error "focusNode: node is hidden!\n"
    Just node -> setNodeFocus (theGraph g) node

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: GraphInfo -- ^ The graph
        -> EdgeId -- ^ ID of the edge
        -> EdgeTypeId -- ^ ID of the edgetype
        -> NodeId -- ^ ID of source node
        -> NodeId -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> IO ()
addEdge gi eId eType nIdFrom nIdTo eName eLabel = do
  g' <- readIORef gi
  g <- case Map.member eId $ edges g' of
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
  writeIORef gi $ g{ edges = Map.insert eId edge $ edges g }

-- | Adds an edge (type name)
addEdge' :: GraphInfo -- ^ The graph
         -> EdgeId -- ^ ID of the edge
         -> String -- ^ Name of the edgetype
         -> NodeId -- ^ ID of source node
         -> NodeId -- ^ ID of target node
         -> String -- ^ Name of the edge
         -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
         -> IO ()
addEdge' gi eId eTypeName nIdFrom nIdTo eName eLable = do
  g <- readIORef gi
  addEdge gi eId (get eTypeName $ edgeType2Id g) nIdFrom nIdTo eName eLable

-- | Adds an compressed edge
addCompressedEdge :: GraphInfo -- ^ The graph
                  -> (NodeId, NodeId, EdgeTypeId) -- ^ source, target, edgetype
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
                      ("",EdgeId 0,Nothing) (nFrom') (nTo')
          return $ Just e
  let edge = GAEdge { udgEdge = edge'
                    , gaeType = eType
                    , ganFrom = nIdFrom
                    , ganTo = nIdTo
                    , gaeValue = ("",EdgeId 0,Nothing)
                    }
  writeIORef gi $ g{ compressedEdges = edge:compressedEdges g }

-- | Deletes an edge
delEdge :: GraphInfo -- ^ The graph
        -> EdgeId -- ^ ID of the node
        -> IO ()
delEdge gi eId = do
  g <- readIORef gi
  case udgEdge $ get eId $ edges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  writeIORef gi $ g{ edges = Map.delete eId $ edges g }

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
      writeIORef gi $ g{ edges = Map.insert eId (edge{ udgEdge = Nothing })
                                               $ edges g }

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
                   -> [EdgeTypeId] -- ^ IDs of the edgetypes to hide
                   -> IO ()
hideSetOfEdgeTypes gi eTypes = do
  g <- readIORef gi
  let (hEdges, sEdges) = Map.foldWithKey (\eid e (he, se) ->
                           if elem (gaeType e) eTypes then (eid:he,se)
                              else (he,eid:se)) ([],[]) $ edges g
  writeIORef gi $ g{ edgeTypes = Map.mapWithKey (\etId et ->
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
  hideSetOfEdgeTypes gi (map (\n -> get n $ edgeType2Id g) eTypeNames)

-- | Checks whether an edge is hidden or not
isHiddenEdge :: GraphInfo -- ^ The graph
             -> EdgeId -- ^ ID of the edge
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
  return $ Map.fold (\edge b -> if b then b else udgEdge edge == Nothing)
                       False $ edges g

-- | Shows a hidden edge again
showEdge :: GraphInfo -- ^ The graph
         -> EdgeId -- ^ ID of the edge
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
          writeIORef gi $ g{ edges = Map.insert eId
                                                   (edge{ udgEdge = Just edge'})
                                                   $ edges g }

-- | Change the edge type of the given edge
changeEdgeType :: GraphInfo -- ^ The graph
               -> EdgeId -- ^ ID of the edge
               -> EdgeTypeId -- ^ ID of the edgetype
               -> IO ()
changeEdgeType gi eId eType = do
  g <- readIORef gi
  let edge = get eId $ edges g
  case eType == (gaeType $ edge) of
    True -> return ()
    False -> do
      case Map.lookup eType $ edgeTypes g of
        Nothing -> error $ "changeEdgeType: unknown EdgeType: " ++ (show eType)
        Just eType' -> do
          case udgEdge edge of
            Nothing -> writeIORef gi $ g{ edges = Map.insert eId
                                         (edge{ gaeType = eType }) $ edges g }
            Just edge' -> do
              deleteArc (theGraph g) edge'
              let Just from = udgNode $ get (ganFrom edge) $ nodes g
                  Just to = udgNode $ get (ganTo edge) $ nodes g
              e <- newArc (theGraph g) (udgEdgeType $ eType') (gaeValue edge)
                          from to
              writeIORef gi $ g{ edges = Map.insert eId
                                                    (edge{ udgEdge = Just e
                                                         , gaeType = eType })
                                                    $ edges g }

-- | Change the edge type of the given edge
changeEdgeType' :: GraphInfo -- ^ The graph
                -> EdgeId -- ^ ID of the edge
                -> String -- ^ Name of the edgetype
                -> IO ()
changeEdgeType' gi eId eTypeName = do
  g <- readIORef gi
  changeEdgeType gi eId (get eTypeName $ edgeType2Id g)

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
