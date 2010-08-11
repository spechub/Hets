{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Interface for graph viewing and abstraction
Copyright   :  (c) Thiemo Wiedemeyer, T. Mossakowski, Uni Bremen 2002-2008
License     :  GPLv2 or higher

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
  , initGraph
  , makeGraph
  , redisplay
    -- * Node interface
  , isHiddenNode
  , focusNode
    -- * Edge interface
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
import GUI.Utils (pulseBar)
import qualified UDrawGraph.Types as DVT
import Events.Destructible as Destructible
import Reactor.BSem

import ATC.DevGraph ()
import Static.DevGraph

import Data.IORef
import Data.List (partition)
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LEdge)
import Data.Maybe (isNothing)

import Control.Monad (foldM)
import Control.Concurrent (threadDelay)

-- | uDrawGraph graph
type OurGraph =
     Graph   DaVinciGraph
             DaVinciGraphParms
             DaVinciNode
             DaVinciNodeType
             DaVinciNodeTypeParms
             DaVinciArc
             DaVinciArcType
             DaVinciArcTypeParms

-- | Node id type
type NodeId = Int

-- | Node value
type NodeValue = (String, NodeId)

-- | Edge value
type EdgeValue = (String, EdgeId, Maybe (LEdge DGLinkLab))

-- | Datastructure for changes, storing all needed information for change
data GAChange
  -- Node changes
  = AddNode NodeId DGNodeType String Bool
  | DelNode NodeId
  | ChangeNodeType NodeId DGNodeType
  | ShowNode NodeId
  | HideNode NodeId
  -- Edge changes
  | AddEdge EdgeId DGEdgeType NodeId NodeId String (Maybe (LEdge DGLinkLab))
            Bool
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

-- | Internal node type
data GANodeType = GANodeType
  { udgNodeType :: DaVinciNodeType NodeValue
  }

-- | Internal edge type
data GAEdgeType = GAEdgeType
  { udgEdgeType :: DaVinciArcType EdgeValue
  , udgCompressed :: (DaVinciArcType EdgeValue, DaVinciArcType EdgeValue)
  , gaeHidden :: Bool
  }

{- | Main datastructure for carrying around the graph,
     both internally (nodes as integers), and at the daVinci level -}
data AbstractionGraph = AbstractionGraph
  { theGraph :: OurGraph
  , nodes :: Map.Map NodeId GANode
  , edges :: Map.Map EdgeId GAEdge
  , nodeTypes :: Map.Map DGNodeType GANodeType
  , edgeTypes :: Map.Map DGEdgeType GAEdgeType
  , compressedEdges :: Map.Map (NodeId, NodeId, DGEdgeType, Bool) GAEdge
  }

-- | IORef for main datastructure
type GraphInfo = IORef AbstractionGraph

instance Eq (DaVinciNode NodeValue) where
    (==) = eq1

instance Eq (DaVinciArc EdgeValue) where
    (==) = eq1

-- | Wrapper for functions with read access
wrapperRead :: (AbstractionGraph -> IO ()) -- ^ Function to call
            -> GraphInfo -- ^ The graph
            -> IO ()
wrapperRead func gi = readIORef gi >>= func

-- | Wrapper for functions with read and write access
wrapperWrite :: (AbstractionGraph -> IO AbstractionGraph) -- ^ Function to call
             -> GraphInfo -- ^ The graph
             -> IO ()
wrapperWrite func gi = do
  g <- readIORef gi
  g' <- func g
  writeIORef gi g'

-- | Wrapper for functions returning a boolean
wrapperBool :: (AbstractionGraph -> Bool) -- ^ Function to call
            -> GraphInfo -- ^ The graph
            -> IO Bool -- ^ Return value
wrapperBool func gi = do
  g <- readIORef gi
  return $ func g

-- | Forces a redraw of the uDrawGraph and wait an amount of time
redisplay' :: AbstractionGraph -- ^ The graph
           -> IO ()
redisplay' g = do
  redraw (theGraph g)
  threadDelay 300000

redisplay :: GraphInfo -- ^ The graph
          -> IO ()
redisplay = wrapperRead redisplay'

-- | Creates an empty graph structure
graphtool :: OurGraph -- ^ uDrawGraph graph
graphtool = daVinciSort

-- | Creates the empty AbstractionGraph
initGraph :: IO GraphInfo -- ^ The graph
initGraph = do
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
makeGraph :: GraphInfo -- ^ The graph
          -> String     -- ^ Title
          -> Maybe (IO ()) -- ^ FileOpen menu
          -> Maybe (IO ()) -- ^ FileSave menu
          -> Maybe (IO ()) -- ^ FileSaveAs menu
          -> IO Bool       -- ^ FileClose menu
          -> Maybe (IO ()) -- ^ FileExit menu
          -> [GlobalMenu] -- ^ Edit menu
          -> [(DGNodeType,DaVinciNodeTypeParms NodeValue)] -- ^ Node types
          -> [(DGEdgeType,DaVinciArcTypeParms EdgeValue)] -- ^ Edge types
          -> String -- ^ Compressed edge color
          -> IO () -- ^ Expand menu action
          -> IO ()
makeGraph gi title open save saveAs close exit menus nTypeParms eTypeParms
          color expand' = do
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
      expand = (LocalMenu (Button "Expand" (const expand')) $$$)
      eTypeParmsCO = map expand eTypeParms'
      eTypeParmsCP = map (expand . (Color color $$$)) eTypeParms'
  graph <- newGraph graphtool graphParms
  nTypes <- mapM (newNodeType graph) nTypeParms'
  eTypes <- mapM (newArcType graph) eTypeParms'
  cTypesO <- mapM (newArcType graph) eTypeParmsCO
  cTypesP <- mapM (newArcType graph) eTypeParmsCP
  writeIORef gi AbstractionGraph
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

{- | similar to lookup (for Map), but returns just the value if lookup was
     successful otherwise an error is raised. -}
get :: (Show k, Ord k) => k -> Map.Map k a -> a
get key = Map.findWithDefault (error $ "get: id unknown: " ++ show key) key

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

-- | Checks whether a node is hidden or not
isHiddenNode' :: AbstractionGraph -- ^ The graph
              -> NodeId -- ^ ID of the node
              -> Bool
isHiddenNode' g nId = isNothing $ udgNode $ get nId $ nodes g

-- | Checks whether a node is hidden or not
isHiddenNode :: GraphInfo -- ^ The graph
             -> NodeId -- ^ ID of the node
             -> IO Bool -- ^ Is hidden
isHiddenNode gi nId = wrapperBool (flip isHiddenNode' nId) gi

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
  case udgNode node of
    Just node' -> setNodeType (theGraph g) node' $ udgNodeType $ get nType
                                                               $ nodeTypes g
    Nothing -> return ()
  return g { nodes = Map.insert nId node { ganType = nType } $ nodes g }

-- | Focus a node
focusNode' :: AbstractionGraph -- ^ The graph
           -> NodeId -- ^ ID of the node
           -> IO ()
focusNode' g nId = maybe (error "focusNode: node is hidden!")
                     (setNodeFocus (theGraph g)) $ udgNode $ get nId $ nodes g

-- | Focus a node
focusNode :: GraphInfo -- ^ The graph
          -> NodeId -- ^ ID of the node
          -> IO ()
focusNode gi nId = wrapperRead (flip focusNode' nId) gi

{- Functions for adding, deleting, changing and hidding edges.-}

-- | Adds an edge (type id)
addEdge :: AbstractionGraph -- ^ The graph
        -> EdgeId -- ^ ID of the edge
        -> DGEdgeType -- ^ ID of the edgetype
        -> NodeId -- ^ ID of source node
        -> NodeId -- ^ ID of target node
        -> String -- ^ Name of the edge
        -> Maybe (LEdge DGLinkLab) -- ^ Label of the edge
        -> Bool -- ^ Hidden
        -> IO AbstractionGraph
addEdge g eId eType nIdFrom nIdTo eName eLabel hidden =
  if Map.member eId $ edges g
    then error $ "addEdge: Edge with id " ++ show eId ++ " already exist!"
    else do
      let gaeV = (eName, eId, eLabel)
      edge' <- if hidden then return Nothing else
        case getEdgeAux g nIdFrom nIdTo eType of
          Just (nFrom, nTo, gaeT) ->
            fmap Just $ newArc (theGraph g) (udgEdgeType gaeT) gaeV nFrom nTo
          Nothing -> return Nothing
      let edge = GAEdge { udgEdge = edge'
                        , gaeType = eType
                        , ganFrom = nIdFrom
                        , ganTo = nIdTo
                        , gaeValue = gaeV }
      return g { edges = Map.insert eId edge $ edges g }

-- | Gets uDrawGraph source and target node, edge type
getEdgeAux :: AbstractionGraph -- ^ The graph
           -> NodeId -- ^ ID of source node
           -> NodeId -- ^ ID of target node
           -> DGEdgeType -- ^ ID of the edgetype
           -> Maybe (DaVinciNode NodeValue, DaVinciNode NodeValue, GAEdgeType)
              -- ^ uDrawGraph source and target node, edge type
getEdgeAux g nIdFrom nIdTo eType =
  let ns = nodes g
      gaeT = get eType $ edgeTypes g
  in case (udgNode $ get nIdFrom ns, udgNode $ get nIdTo ns) of
    (Just nFrom, Just nTo) | f gaeT nIdFrom nIdTo -> Just (nFrom, nTo, gaeT)
    _ -> Nothing
  where
    f et nf nt = not (gaeHidden et || isHiddenNode' g nf || isHiddenNode' g nt)

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
                  -> (NodeId, NodeId, DGEdgeType, Bool) -- ^ Compressed edge id
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
                  -> (NodeId, NodeId, DGEdgeType, Bool) -- ^ Compressed edge id
                  -> IO AbstractionGraph
delCompressedEdge g ce  = do
  case udgEdge $ get ce $ compressedEdges g of
    Just edge -> deleteArc (theGraph g) edge
    Nothing -> return ()
  return g { compressedEdges = Map.delete ce $ compressedEdges g }

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

-- | Hides a set of edgetypes (type ids)
hideSetOfEdgeTypes :: GraphInfo -- ^ The graph
                   -> [DGEdgeType] -- ^ IDs of the edgetypes to hide
                   -> IO ()
hideSetOfEdgeTypes gi eT = do
  (update, exit) <- pulseBar "Updating graph" "hiding/showing edge types..."
  wrapperWrite (flip hideSetOfEdgeTypes' eT) gi
  update "finished"
  exit

-- | Checks whether an edge is hidden or not
isHiddenEdge' :: AbstractionGraph -- ^ The graph
              -> EdgeId -- ^ ID of the edge
              -> Bool -- ^ Is edge hidden
isHiddenEdge' g eId = isNothing $ udgEdge $ get eId $ edges g

-- | Checks whether an edge is hidden or not
isHiddenEdge :: GraphInfo -- ^ The graph
             -> EdgeId -- ^ ID of the edge
             -> IO Bool -- ^ Is edge hidden
isHiddenEdge gi eId = wrapperBool (flip isHiddenEdge' eId) gi

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

-- | Apply changes to the uDrawGraph graph
applyChanges' :: AbstractionGraph -- ^ The graph
              -> [DGChange] -- ^ List of changes
              -> [NodeId] -- ^ IDs of the nodes to hide
              -> [EdgeId] -- ^ IDs of the edges to hide
              -> [(NodeId, NodeId, DGEdgeType, Bool)] -- ^ A list of new edges
              -> IO AbstractionGraph
applyChanges' g dgchanges hnIds heIds' ce = do
  let
    -- split and convert changes
    (an',dn,cnt',ae',de) = convertChanges dgchanges ([],[],[],[],[])
    -- get Ids
    anIds = map (\(AddNode nId _ _ _) -> nId) an'
    dnIds = map (\(DelNode nId) -> nId) dn
    aeIds = map (\(AddEdge eId _ _ _ _ _ _) -> eId) ae'
    deIds = map (\(DelEdge eId) -> eId) de
    heIds = heIds' ++ map fst (filter (\ (eId,e) -> notElem eId deIds &&
      notElem eId heIds' && (elem (ganTo e) hnIds || elem (ganFrom e) hnIds))
      $ Map.toList $ edges g)
    -- filter multiple changes and changes for deleted and new nodes
    (cnt, new) = partition (\(ChangeNodeType nId _) -> notElem nId anIds)
      $ filter (\(ChangeNodeType nId _) -> notElem nId dnIds) $ fst
      $ foldl (\(cs, nIds) c@(ChangeNodeType nId _) -> if elem nId nIds
                then (cs, nIds) else (c:cs, nId:nIds)) ([],[]) $ reverse cnt'
    -- fuction for geting new nt if node type change is submitted for node
    nnT nId nT =  foldl (\nT' (ChangeNodeType nId' nT'') ->
                              if nId == nId' then nT'' else nT') nT new
    -- update node type and mark as hidden if they would be hidden afterwards
    an = map (\(AddNode nId nT nN _) -> AddNode nId (nnT nId nT) nN
                                                $ elem nId hnIds) an'
    -- old compressed edges
    oce = Map.keys $ compressedEdges g
    -- delete compressed edges not needed anymore
    dce = foldl (\es e -> if elem e ce then es else DelCompEdge e:es) [] oce
    -- get hidden nodes that are not hidden after update
    sn = map ShowNode $ filter
             (\n -> isHiddenNode' g n && not (elem n hnIds || elem n dnIds))
             $ Map.keys $ nodes g
    -- edges to hide
    he = map HideEdge $ filter
             (\eId -> notElem eId aeIds && not (isHiddenEdge' g eId)) heIds
    -- mark as hidden if they would be hidden afterwards
    ae = map (\(AddEdge eId eT nIdF nIdT eN eL _) ->
      AddEdge eId eT nIdF nIdT eN eL $ elem nIdF hnIds || elem nIdT hnIds ||
                                       elem eId heIds) ae'
    -- nodes to hide
    hn = map HideNode $ filter
             (\nId -> notElem nId anIds && not (isHiddenNode' g nId)) hnIds
    -- edges to show
    se = map ShowEdge
      $ filter (\ e -> isHiddenEdge' g e && notElem e heIds && notElem e deIds)
      $ Map.keys $ edges g
    -- get compressed edges to add
    ace = foldl (\es e -> if elem e oce then es else AddCompEdge e:es) [] ce
    -- concat changes
    changes = de ++ dce ++ dn ++ cnt ++ sn ++ an ++ he ++ hn ++ se ++ ae ++ ace
  foldM applyChange g changes

-- | Apply changes to the uDrawGraph graph
applyChanges :: GraphInfo -- ^ The graph
             -> [DGChange] -- ^ List of changes
             -> [NodeId] -- ^ IDs of the nodes to hide
             -> [EdgeId] -- ^ IDs of the edges to hide
             -> [(NodeId, NodeId, DGEdgeType, Bool)] -- ^ A list of new edges
             -> IO ()
applyChanges gi changes nIds eIds compedges = do
  (update, exit) <- pulseBar "Updating graph" "applying changes..."
  wrapperWrite (\ g -> applyChanges' g changes nIds eIds compedges) gi
  update "finished"
  exit

-- | Converts and splits DGChanges to GAChanges
convertChanges :: [DGChange] -- ^ Development graph changes
               -> ([GAChange], [GAChange], [GAChange], [GAChange], [GAChange])
                  -- ^ Graph abstraction changes
               -> ([GAChange], [GAChange], [GAChange], [GAChange], [GAChange])
                  -- ^ Graph abstraction changes
convertChanges [] changes = changes
convertChanges (c:r) (an, dn, cnt, ae, de) = case change of
  AddNode _ _ _ _       -> convertChanges r (change : an, dn, cnt, ae, de)
  DelNode _             -> convertChanges r (an, change : dn, cnt, ae, de)
  ChangeNodeType _ _    -> convertChanges r (an, dn, change : cnt, ae, de)
  AddEdge _ _ _ _ _ _ _ -> convertChanges r (an, dn, cnt, change : ae, de)
  DelEdge _             -> convertChanges r (an, dn, cnt, ae, change : de)
  _                     -> error "convertChanges: internal error!"
  where
    change = convertChange c

-- | Converts a DGChange to a GAChange
convertChange :: DGChange -- ^ Development graph change
              -> GAChange -- ^ Graph abstraction change
convertChange change = case change of
  InsertNode (node, nodelab) ->
    AddNode node (getRealDGNodeType nodelab) (getDGNodeName nodelab) False
  DeleteNode (node, _) ->
    DelNode node
  SetNodeLab _ (node, newLab) ->
    ChangeNodeType node $ getRealDGNodeType newLab
  InsertEdge e@(src, tgt, lbl) ->
    AddEdge (dgl_id lbl) (getRealDGLinkType lbl) src tgt "" (Just e) False
  DeleteEdge (_, _, lbl) ->
    DelEdge $ dgl_id lbl

-- | Applies a change to the graph
applyChange :: AbstractionGraph -- ^ The graph
            -> GAChange -- ^ Change to apply
            -> IO AbstractionGraph
applyChange g change = case change of
  AddNode nId nT nN nH              -> addNode g nId nT nN nH
  DelNode nId                       -> delNode g nId
  ChangeNodeType nId nT             -> changeNodeType g nId nT
  ShowNode nId                      -> showNode g nId
  HideNode nId                      -> hideNode g nId
  AddEdge eId eT nIdF nIdT eN eL eH -> addEdge g eId eT nIdF nIdT eN eL eH
  DelEdge eId                       -> delEdge g eId
  ShowEdge eId                      -> showEdge g eId
  HideEdge eId                      -> hideEdge g eId
  AddCompEdge ceId                  -> addCompressedEdge g ceId
  DelCompEdge ceId                  -> delCompressedEdge g ceId

-- | Converts a DGraph to a list of changes
convert :: DGraph -- ^ The development graph
        -> [DGChange]  -- ^ List of changes
convert dg = map InsertNode (labNodesDG dg)
          ++ map InsertEdge (labEdgesDG dg)

-- * direct manipulation of uDrawGraph

-- | execute in the context of the given graph
doInGraphContext :: DVT.DaVinciCmd -- ^ uDrawGraph command
                 -> GraphInfo -- ^ The graph
                 -> IO ()
doInGraphContext cmd gi = do
  g <- readIORef gi
  let Graph dg = theGraph g
  synchronize (pendingChangesLock dg) $ doInContext cmd
    $ getDaVinciGraphContext dg

-- | Improve the layout of a graph like calling \"Layout->Improve All\"
layoutImproveAll :: GraphInfo -- ^ The graph
                 -> IO ()
layoutImproveAll = doInGraphContext (DVT.Menu $ DVT.Layout DVT.ImproveAll)

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
destroyGraph :: OurGraph  -- ^ uDrawGraph graph
             -> IO ()
destroyGraph (Graph dg) = destroy $ getDaVinciGraphContext dg
