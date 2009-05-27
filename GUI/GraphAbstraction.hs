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
    NodeId
  , NodeValue
  , EdgeValue
  , GraphInfo
  -- * Creation and display
  , initgraphs
  , makegraph
  , redisplay
  , showAll
  -- * Node interface
  , hideNodes
  , isHiddenNode
  , hasHiddenNodes
  , focusNode
  -- * Edge interface
  , hideEdges
  , hideSetOfEdgeTypes
  , isHiddenEdge
  -- * Conversion and update of graph
  , applyChanges
  , convert
  -- * Direct manipulation of uDrawGraph
  , layoutImproveAll
  , showTemporaryMessage
  , deactivateGraphWindow
  , activateGraphWindow
  , closeGraphWindow
  ) where

import GUI.UDGUtils
import GUI.Utils
import qualified UDrawGraph.Types as DVT
import qualified UDrawGraph.Basic as DVB
import Events.Destructible as Destructible
import Reactor.BSem

import ATC.DevGraph ()
import Static.DevGraph

import Data.IORef
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LEdge, LNode)
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Maybe (isNothing)

import Control.Monad (foldM)
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

data GAChange
  -- Node changes
  = AddNode NodeId DGNodeType String Bool
  | DelNode NodeId
  | ChangeNodeType NodeId DGNodeType
  | ShowNode NodeId
  | HideNode NodeId
  -- Edge changes
  | AddEdge EdgeId DGEdgeType NodeId NodeId String (Maybe (LEdge DGLinkLab))
  | DelEdge EdgeId
  | ShowEdge EdgeId
  | HideEdge EdgeId
  -- Compressed edge changes
  | AddCompEdge (NodeId, NodeId, DGEdgeType, Bool)
  | DelCompEdge (NodeId, NodeId, DGEdgeType, Bool)

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
  , compressedEdges :: Map.Map (NodeId, NodeId, DGEdgeType, Bool) GAEdge
  }

type GraphInfo = IORef AbstractionGraph

instance Eq (DaVinciNode NodeValue) where
    (==) = eq1

instance Eq (DaVinciArc EdgeValue) where
    (==) = eq1

wrapperRead :: (AbstractionGraph -> IO ())
            -> GraphInfo
            -> IO ()
wrapperRead func gi = do
  g <- readIORef gi
  func g

wrapperWrite :: (AbstractionGraph -> IO AbstractionGraph)
             -> GraphInfo
             -> IO ()
wrapperWrite func gi = do
  g <- readIORef gi
  g' <- func g
  writeIORef gi g'

wrapperBool :: (AbstractionGraph -> Bool)
            -> GraphInfo
            -> IO Bool
wrapperBool func gi = do
  g <- readIORef gi
  return $ func g

-- | Forces a redraw of the uDrawGraph and wait an amount of time
redisplay' :: AbstractionGraph -> IO ()
redisplay' g = do
  redraw (theGraph g)
  threadDelay 300000

redisplay :: GraphInfo -> IO ()
redisplay = wrapperRead redisplay'

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
            , compressedEdges = Map.empty
            }
  newIORef g

-- | Creates the uDrawGraph graph
makegraph :: GraphInfo
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
makegraph gi title open save saveAs close exit menus nTypeParms eTypeParms = do
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
      (nTypeNames,nTypeParms') = unzip nTypeParms
      (eTypeNames,eTypeParms') = unzip eTypeParms
      expand = (LocalMenu (Button "Expand" (\ _ -> do
                                             g <- readIORef gi
                                             g' <- showAll' g
                                             writeIORef gi g'
                                             redisplay' g')) $$$)
      eTypeParmsCO = map expand eTypeParms'
      eTypeParmsCP = map expand $ map (Color "purple2" $$$) eTypeParms'
  graph <- newGraph graphtool graphParms
  nTypes <- mapM (newNodeType graph) nTypeParms'
  eTypes <- mapM (newArcType graph) eTypeParms'
  cTypesO <- mapM (newArcType graph) eTypeParmsCO
  cTypesP <- mapM (newArcType graph) eTypeParmsCP
  writeIORef gi $ AbstractionGraph
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
    , compressedEdges = Map.empty
    }

{- similar to lookup (for Map), but returns just the value if lookup was
   successful otherwise an error is raised. -}
get :: (Show k, Ord k) => k -> Map.Map k a -> a
get key = Map.findWithDefault (error $ "get: id unknown: " ++ show key) key

-- | Shows all hidden nodes and edges
showAll' :: AbstractionGraph -- ^ The graph
         -> IO AbstractionGraph
showAll' g = do
  g' <- delCompressedEdges g
  g'' <- foldM showNode g' $ filter (isHiddenNode' g') $ Map.keys $ nodes g'
  foldM showEdge g'' $ filter (isHiddenEdge' g'') $ Map.keys $ edges g''

showAll :: GraphInfo -> IO ()
showAll = wrapperWrite showAll'

{- Functions for adding, deleting, changing and hidding nodes.-}

-- | Adds a node (type id)
addNode :: AbstractionGraph -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> DGNodeType -- ^ ID of the nodetype
        -> String -- ^ Name of the node
        -> Bool -- ^ Hidden
        -> IO AbstractionGraph
addNode g nId nType nName hidden = if Map.member nId $ nodes g
  then error $ "addNode: Node with id " ++ show nId ++ " already exist!"
  else do
    node' <- if hidden then return Nothing else do
      node'' <- newNode (theGraph g) (udgNodeType $ get nType $ nodeTypes g)
                        (nName,nId)
      return $ Just node''
    let node = GANode { udgNode = node'
                      , ganType = nType
                      , ganValue = (nName, nId)
                      }
    return g { nodes = Map.insert nId node $ nodes g }

-- | Deletes a node
delNode :: AbstractionGraph -- ^ The graph
        -> NodeId -- ^ ID of the node
        -> IO AbstractionGraph
delNode g nId = do
  case udgNode $ get nId $ nodes g of
    Just node -> deleteNode (theGraph g) node
    Nothing -> return ()
  return g { nodes = Map.delete nId $ nodes g }

-- | Hides a node
hideNode :: AbstractionGraph -- ^ The graph
         -> NodeId -- ^ ID of the node
         -> IO AbstractionGraph
hideNode g nId = do
  let node = get nId $ nodes g
  case udgNode node of
    Nothing -> return g
    Just node' -> do
      deleteNode (theGraph g) node'
      return g { nodes = Map.insert nId node {udgNode = Nothing} $ nodes g }

-- | Hides a set of nodes
hideNodes' :: AbstractionGraph -- ^ The graph
           -> [NodeId] -- ^ IDs of the nodes to hide
           -> [(NodeId, NodeId, DGEdgeType, Bool)] -- ^ A list of new edges
           -> IO AbstractionGraph
hideNodes' g nIds compedges = do
  g' <- showAll' g
  g'' <- hideEdgesOfNodes g' nIds
  g''' <- foldM hideNode g'' nIds
  foldM addCompressedEdge g''' compedges

hideNodes :: GraphInfo -> [NodeId] -> [(NodeId, NodeId, DGEdgeType, Bool)]
          -> IO ()
hideNodes gi nId comp = wrapperWrite (\ g -> hideNodes' g nId comp) gi

-- | Checks whether a node is hidden or not
isHiddenNode' :: AbstractionGraph -- ^ The graph
              -> NodeId -- ^ ID of the node
              -> Bool
isHiddenNode' g nId = isNothing $ udgNode $ get nId $ nodes g

isHiddenNode :: GraphInfo -> NodeId -> IO Bool
isHiddenNode gi nId = wrapperBool (\ g -> isHiddenNode' g nId) gi

-- | Checks if at least one hidden node exists
hasHiddenNodes' :: AbstractionGraph -- ^ The graph
                -> Bool
hasHiddenNodes' = Map.fold (\ n b -> b || isNothing (udgNode n)) False . nodes

hasHiddenNodes :: GraphInfo -> IO Bool
hasHiddenNodes = wrapperBool hasHiddenNodes'

-- | Shows a hidden node again
showNode :: AbstractionGraph -- ^ The graph
         -> NodeId -- ^ ID of the node
         -> IO AbstractionGraph
showNode g nId = do
  let node = get nId $ nodes g
  case udgNode node of
    Just _ -> return g
    Nothing -> do
      node' <- newNode (theGraph g)
                       (udgNodeType $ get (ganType node) $ nodeTypes g)
                       $ ganValue node
      return
        g { nodes = Map.insert nId node { udgNode = Just node' } $ nodes g }

-- | Change the node type of the given node
changeNodeType :: AbstractionGraph -- ^ The graph
               -> NodeId -- ^ ID of the node
               -> DGNodeType -- ^ ID of the nodetype
               -> IO AbstractionGraph
changeNodeType g nId nType = do
  let node = get nId $ nodes g
  case udgNode $ node of
    Just node' -> setNodeType (theGraph g) node' $ udgNodeType $ get nType
                                                               $ nodeTypes g
    Nothing -> return ()
  return g { nodes = Map.insert nId node { ganType = nType } $ nodes g }

-- | Focus a node
focusNode' :: AbstractionGraph -- ^ The graph
           -> NodeId -- ^ ID of the node
           -> IO ()
focusNode' g nId = do
  case udgNode $ get nId $ nodes g of
    Nothing -> errorDialog "Error" "focusNode: node is hidden!"
    Just node -> setNodeFocus (theGraph g) node

focusNode :: GraphInfo -> NodeId -> IO ()
focusNode gi nId = wrapperRead (\ g -> focusNode' g nId) gi

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: AbstractionGraph -- ^ The graph
        -> EdgeId -- ^ ID of the edge
        -> DGEdgeType -- ^ ID of the edgetype
        -> NodeId -- ^ ID of source node
        -> NodeId -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> IO AbstractionGraph
addEdge g eId eType nIdFrom nIdTo eName eLabel = if Map.member eId $ edges g
  then error $ "addEdge: Edge with id " ++ show eId ++ " already exist!"
  else do
    let gaeV = (eName, eId, eLabel)
    edge' <- case getEdgeAux g nIdFrom nIdTo eType of
      Just (nFrom, nTo, gaeT) ->
        fmap Just $ newArc (theGraph g) (udgEdgeType gaeT) gaeV nFrom nTo
      Nothing -> return Nothing
    let edge = GAEdge { udgEdge = edge'
                      , gaeType = eType
                      , ganFrom = nIdFrom
                      , ganTo = nIdTo
                      , gaeValue = gaeV }
    return g { edges = Map.insert eId edge $ edges g }

getEdgeAux :: AbstractionGraph
           -> NodeId
           -> NodeId
           -> DGEdgeType
           -> Maybe (DaVinciNode NodeValue, DaVinciNode NodeValue, GAEdgeType)
getEdgeAux g nIdFrom nIdTo eType =
  let ns = nodes g
      gaeT = get eType $ edgeTypes g
  in case (udgNode $ get nIdFrom ns, udgNode $ get nIdTo ns) of
    (Just nFrom, Just nTo) | f gaeT nIdFrom nIdTo -> Just (nFrom, nTo, gaeT)
    _ -> Nothing
  where f = (\et nf nt -> not (gaeHidden et || isHiddenNode' g nf
                                            || isHiddenNode' g nt))

-- | Deletes an edge
delEdge :: AbstractionGraph -- ^ The graph
        -> EdgeId -- ^ ID of the node
        -> IO AbstractionGraph
delEdge g eId = do
  case udgEdge $ get eId $ edges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  return g { edges = Map.delete eId $ edges g }

-- | Adds an compressed edge
addCompressedEdge :: AbstractionGraph -- ^ The graph
                  -> (NodeId, NodeId, DGEdgeType, Bool) -- ^ src,tar,et,orig
                  -> IO AbstractionGraph
addCompressedEdge g ce@(nIdFrom, nIdTo, eType, orig) = do
  let gaeV = ("", EdgeId 0, Nothing)
  edge' <- case getEdgeAux g nIdFrom nIdTo eType of
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
  return g { compressedEdges = Map.insert ce edge $ compressedEdges g }

-- | Deletes an compressed edge
delCompressedEdge :: AbstractionGraph -- ^ The graph
                  -> (NodeId, NodeId, DGEdgeType, Bool)
                  -> IO AbstractionGraph
delCompressedEdge g ce  = do
  case udgEdge $ get ce $ compressedEdges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  return g { compressedEdges = Map.delete ce $ compressedEdges g }

-- | Deletes an compressed edge
delCompressedEdges :: AbstractionGraph -- ^ The graph
                   -> IO AbstractionGraph
delCompressedEdges g = do
  mapM_ (\ e -> case udgEdge e of
          Just edge -> deleteArc (theGraph g) edge
          Nothing -> return ()) $ Map.elems $ compressedEdges g
  return g { compressedEdges = Map.empty }

-- | Hides an edge
hideEdge :: AbstractionGraph -- ^ The graph
         -> EdgeId -- ^ ID of the edge
         -> IO AbstractionGraph
hideEdge g eId = do
  let edge = get eId $ edges g
  case udgEdge edge of
    Nothing -> return g
    Just edge' -> do
      deleteArc (theGraph g) edge'
      return g { edges = Map.insert eId edge { udgEdge = Nothing } $ edges g }

hideEdges' :: AbstractionGraph -> [EdgeId] -> IO AbstractionGraph
hideEdges' = foldM hideEdge

hideEdges :: GraphInfo -> [EdgeId] -> IO ()
hideEdges gi eIds = wrapperWrite (\ g -> hideEdges' g eIds) gi

-- | Hides incoming and outgoing edges of nodes
hideEdgesOfNodes :: AbstractionGraph -- ^ The graph
                 -> [NodeId] -- ^ IDs of the nodes to hide
                 -> IO AbstractionGraph
hideEdgesOfNodes g nIds = do
  foldM hideEdge g $ map fst
        $ filter (\ (_,e) -> elem (ganTo e) nIds || elem (ganFrom e) nIds)
        $ Map.toList $ edges g

-- | Hides a set of edgetypes (type ids)
hideSetOfEdgeTypes' :: AbstractionGraph -- ^ The graph
                    -> [DGEdgeType] -- ^ IDs of the edgetypes to hide
                    -> IO AbstractionGraph
hideSetOfEdgeTypes' g eTypes = do
  let (hEdges, sEdges) = Map.foldWithKey (\ eid e (he, se) ->
         if elem (gaeType e) eTypes then (eid : he, se) else (he, eid : se))
         ([], []) $ edges g'
      g' = g { edgeTypes = Map.mapWithKey
             (\ etId et -> et { gaeHidden = elem etId eTypes }) $ edgeTypes g }
  g'' <- foldM hideEdge g' hEdges
  foldM showEdge g'' sEdges

hideSetOfEdgeTypes :: GraphInfo -> [DGEdgeType] -> IO ()
hideSetOfEdgeTypes gi eT = wrapperWrite (\g -> hideSetOfEdgeTypes' g eT) gi

-- | Checks whether an edge is hidden or not
isHiddenEdge' :: AbstractionGraph -- ^ The graph
              -> EdgeId -- ^ ID of the edge
              -> Bool
isHiddenEdge' g eId = isNothing $ udgEdge $ get eId $ edges g

isHiddenEdge :: GraphInfo -> EdgeId -> IO Bool
isHiddenEdge gi eId = wrapperBool (\ g -> isHiddenEdge' g eId) gi

-- | Shows a hidden edge again
showEdge :: AbstractionGraph -- ^ The graph
         -> EdgeId -- ^ ID of the edge
         -> IO AbstractionGraph
showEdge g eId = do
  let es = edges g
      edge = get eId es
  case udgEdge edge of
    Just _ -> return g
    Nothing -> case getEdgeAux g (ganFrom edge) (ganTo edge) (gaeType edge) of
      Just (nFrom, nTo, gaeT) -> do
        edge' <- newArc (theGraph g) (udgEdgeType gaeT) (gaeValue edge) nFrom
                        nTo
        return g { edges = Map.insert eId edge { udgEdge = Just edge' } es }
      Nothing -> return g

-- * Conversion and update of graph

-- | apply the changes of first history item (computed by proof rules,
-- see folder Proofs) to the displayed development graph
applyChanges' :: AbstractionGraph
              -> [DGChange]
              -> [NodeId] -- ^ IDs of the nodes to hide
              -> [(NodeId, NodeId, DGEdgeType, Bool)] -- ^ A list of new edges
              -> IO AbstractionGraph
applyChanges' g dgchanges hn' ce' = do
  -- 1. Split and convert changes and filter duplicated node type changes
  let (an,dn,cnt',ae,de) = convertChanges dgchanges ([],[],[],[],[])
      (cnt,_) = foldl (\(cs, nIds) c@(ChangeNodeType nId _) -> if elem nId nIds
                  then (cs, nIds) else (c:cs, nId:nIds)) ([], []) $ reverse cnt'
  -- 2. Delete edges
  g1 <- foldM applyChange g de
  -- 3. Delete compressed edges
  g2 <- foldM applyChange g1
    $ foldl (\cs ce -> if notElem ce ce' then DelCompEdge ce : cs else cs) []
    $ Map.keys $ compressedEdges g1
  -- 4. Delete nodes
  g3 <- foldM applyChange g2 dn
  -- 5. Change nodeTypes
  g4 <- foldM applyChange g3 cnt
  -- 6. Show nodes
  g5 <- foldM applyChange g4 $ map (\n -> ShowNode n)
    $ filter (\ n -> isHiddenNode' g4 n && notElem n hn') $ Map.keys $ nodes g4
  -- 7. Add nodes
  g6 <- foldM applyChange g5
    $ map (\ (AddNode nId nT nN _) -> AddNode nId nT nN $ elem nId hn') an
  -- 8. Hide nodes
  g7 <- foldM applyChange g6 $ map (\n -> HideNode n) hn'
  -- 9. Show edges
  g8 <- foldM applyChange g7 $ map (\e -> ShowEdge e)
    $ filter (isHiddenEdge' g7) $ Map.keys $ edges g7
  -- 10. Add edges
  g9 <- foldM applyChange g8 ae
  -- 11. Add compressed edges
  let ce'' = Map.keys $ compressedEdges g9
  foldM applyChange g9
    $ foldl (\cs ce -> if elem ce ce'' then cs else AddCompEdge ce : cs) [] ce'

applyChanges :: GraphInfo -> [DGChange] -> [NodeId]
             -> [(NodeId, NodeId, DGEdgeType, Bool)] -> IO ()
applyChanges gi changes nIds compedges =
  wrapperWrite (\ g -> applyChanges' g changes nIds compedges) gi

convertChanges :: [DGChange]
               -> ([GAChange], [GAChange], [GAChange], [GAChange], [GAChange])
               -> ([GAChange], [GAChange], [GAChange], [GAChange], [GAChange])
convertChanges [] changes = changes
convertChanges (c:r) (an, dn, cnt, ae, de) = case change of
  AddNode _ _ _ _     -> convertChanges r (change : an, dn, cnt, ae, de)
  DelNode _           -> convertChanges r (an, change : dn, cnt, ae, de)
  ChangeNodeType _ _  -> convertChanges r (an, dn, change : cnt, ae, de)
  AddEdge _ _ _ _ _ _ -> convertChanges r (an, dn, cnt, change : ae, de)
  DelEdge _           -> convertChanges r (an, dn, cnt, ae, change : de)
  _                   -> error "convertChanges: internal error!"
  where
    change = convertChange c

convertChange :: DGChange
              -> GAChange
convertChange change = case change of
  InsertNode (node, nodelab) ->
    AddNode node (getRealDGNodeType nodelab) (getDGNodeName nodelab) False
  DeleteNode (node, _) ->
    DelNode node
  SetNodeLab _ (node, newLab) ->
    ChangeNodeType node $ getRealDGNodeType newLab
  InsertEdge e@(src, tgt, lbl) ->
    AddEdge (dgl_id lbl) (getRealDGLinkType lbl) src tgt "" $ Just e
  DeleteEdge (_, _, lbl) ->
    DelEdge $ dgl_id lbl

applyChange :: AbstractionGraph -> GAChange -> IO AbstractionGraph
applyChange g change = case change of
  AddNode nId nT nN nH           -> addNode g nId nT nN nH
  DelNode nId                    -> delNode g nId
  ChangeNodeType nId nT          -> changeNodeType g nId nT
  ShowNode nId                   -> showNode g nId
  HideNode nId                   -> hideNode g nId
  AddEdge eId eT nIdF nIdT eN eL -> addEdge g eId eT nIdF nIdT eN eL
  DelEdge eId                    -> delEdge g eId
  ShowEdge eId                   -> showEdge g eId
  HideEdge eId                   -> hideEdge g eId
  AddCompEdge ceId               -> addCompressedEdge g ceId
  DelCompEdge ceId               -> delCompressedEdge g ceId

convert' :: AbstractionGraph -> DGraph -> IO AbstractionGraph
convert' g dg = do
  g' <- convertNodes g dg
  convertEdges g' dg

convert :: GraphInfo -> DGraph -> IO ()
convert gi dg = wrapperWrite (\ g -> convert' g dg) gi

{- | converts the nodes of the development graph, if it has any,
and returns the resulting conversion maps
if the graph is empty the conversion maps are returned unchanged-}
convertNodes :: AbstractionGraph -> DGraph -> IO AbstractionGraph
convertNodes g = foldM convertNodesAux g . labNodesDG

{- | auxiliary function for convertNodes if the given list of nodes is
emtpy, it returns the conversion maps unchanged otherwise it adds the
converted first node to the abstract graph and to the affected
conversion maps and afterwards calls itself with the remaining node
list -}
convertNodesAux :: AbstractionGraph -> LNode DGNodeLab -> IO AbstractionGraph
convertNodesAux g (node, dgnode) =
  addNode g node (getRealDGNodeType dgnode) (getDGNodeName dgnode) False

{- | converts the edges of the development graph
works the same way as convertNods does-}
convertEdges :: AbstractionGraph -> DGraph -> IO AbstractionGraph
convertEdges g = foldM convertEdgesAux g . labEdgesDG

-- | auxiliary function for convertEges
convertEdgesAux :: AbstractionGraph -> LEdge DGLinkLab -> IO AbstractionGraph
convertEdgesAux g e@(src, tar, lbl) =
  addEdge g (dgl_id lbl) (getRealDGLinkType lbl) src tar "" $ Just e

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
closeGraphWindow gi = readIORef gi >>= destroyGraph . theGraph

-- | destroy graph
destroyGraph :: OurGraph -> IO ()
destroyGraph (Graph dg) = destroy $ getDaVinciGraphContext dg
