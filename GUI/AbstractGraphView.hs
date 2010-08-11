{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Interface for graph viewing and abstraction
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2007
License     :  GPLv2 or higher

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (relies on Logic via DevGraph)

Interface for graph viewing and abstraction.
   It is possible to hide sets of nodes and edges.
   Using a composition table for edge types,
   paths through hidden nodes can be displayed.
   Graphs, nodes, and edges are handled via
   descriptors (here: integers), while node and
   edge types are handled by user-supplied strings.
-}

module GUI.AbstractGraphView
    ( OurGraph
    , initgraphs
    , Result(Result)
    , makegraph
    , makegraphExt
    , redisplay
    , getGraphid
    , Descr
    , GraphInfo
    , RelationViewSpec(RelViewSpec)
    , writeRelViewSpecs
    , AbstractionGraph(theGraph, edges,
                       ontoGraph, nodeMap, nodes, relViewSpecs)
    , NodeMapping
    , writeNodeMap
    , addnode
    , addlink
    , delnode
    , dellink
    , EdgeValue
    , writeOntoGraph
    , showIt
    , CompTable
    , hidenodes
    , changeNodeType
    , checkHasHiddenNodes
    , hideSetOfNodeTypes
    , hideSetOfEdgeTypes
    -- * Direct manipulation of uDrawGraph
    , layoutImproveAll
    , showTemporaryMessage
    , deactivateGraphWindow
    , activateGraphWindow
    ) where

import GUI.UDGUtils
import qualified UDrawGraph.Types as DVT

import ATC.DevGraph()
import Static.DevGraph (DGLinkLab)

import Common.Taxonomy
import Common.Lib.Graph as Tree

import Data.IORef
import Data.List(nub)
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LEdge)
import qualified Data.Graph.Inductive.Graph as Graph

import Control.Concurrent

-- | wait for this amount of microseconds to let uDrawGraph redraw
delayTime :: Int
delayTime = 300000

{- methods using fetchGraph return a quadruple containing the
modified graph, a descriptor of the last modification (e.g. a new
node), the descriptor that can be used for the next modification and a
possible error message -}

-- Which graph display tool to be used, perhaps make it more tool independent?

instance Eq (DaVinciNode (String,Int,Int)) where
    (==) = eq1

instance Eq (DaVinciArc EdgeValue) where
    (==) = eq1

graphtool :: OurGraph
graphtool = daVinciSort

type OurGraph =
     Graph   DaVinciGraph
             DaVinciGraphParms
             DaVinciNode
             DaVinciNodeType
             DaVinciNodeTypeParms
             DaVinciArc
             DaVinciArcType
             DaVinciArcTypeParms

-- Main datastructure for carrying around the graph,
-- both internally (nodes as integers), and at the daVinci level

type CompTable = [(String,String,String)]
data AbstractionGraph = AbstractionGraph
  { theGraph :: OurGraph
  , nodeTypes :: [(String,DaVinciNodeType (String,Int,Int))]
  , edgeTypes :: [(String,DaVinciArcType EdgeValue)]
  , nodes :: Map.Map Int (String, DaVinciNode (String,Int,Int))
  , edges :: Map.Map Int (Int, Int, String, DaVinciArc EdgeValue)
  {- probably, also the abstracted graph needs to be stored,
     and a list of hide/abstract events with the hidden nodes/edges (for
     each event), which is used to restore things when showIt is called -}
  , edgeComp :: CompTable
  , eventTable :: [(Int,Entry)]
  , hiddenEdges :: [(Int,(Int, Int, String, DaVinciArc EdgeValue))]
  , deletedNodes :: [Int]
  , ontoGraph :: Tree.Gr (String,String,OntoObjectType) String
  , relViewSpecs :: [RelationViewSpec]
  , nodeMap :: NodeMapping
  }

type NodeMapping = Map.Map Int Descr
type Descr = Int
type EdgeValue = (String,Int,Maybe (LEdge DGLinkLab))
type GraphInfo = IORef ([(Descr,AbstractionGraph)],Descr)
                       -- for each graph the descriptor and the graph,
                       -- plus a global counter for new descriptors
data Result = Result Descr          -- graph, node or edge descriptor
                     (Maybe String) -- a possible error message


data Entry = Entry {newNodes :: [(Descr,(String,
                                         DaVinciNode (String,Int,Int)))],
                    oldNodes :: [(Descr,(String,String))],
                    newEdges :: [(Int,(Int,Int,String,DaVinciArc EdgeValue))],
                    oldEdges :: [(Int,(Int,Int,String,EdgeValue))]
                    }

data RelationViewSpec = RelViewSpec String Bool Bool

{- creates a new entry of the eventTable and fills it with the data contained
   in its parameters -}
createEntry :: [(Descr,(String,DaVinciNode (String,Int,Int)))]
            -> [(Descr,(String,String))]
            -> [(Descr,(Int,Int,String,DaVinciArc EdgeValue))]
            -> [(Descr,(Int,Int,String,EdgeValue))] -> Descr -> (Int,Entry)
createEntry nn on ne oe cnt =
  (cnt, Entry {newNodes = nn, oldNodes = on, newEdges = ne, oldEdges = oe})

{- zips two lists by pairing each element of the first with each element of
   the second -}
specialzip :: [a] -> [b] -> [(a,b)]
specialzip xs ys = [ (x, y) | x <- xs, y <- ys ]

{- similar to lookup, but also returns the decriptor
   should only be used, if lookup will be successful (otherwise an error is
   thrown) -}
get :: Descr -> [(Descr, a)] -> (Descr,a)
get d list =
  case lookup d list of
    Just r -> (d, r)
    Nothing -> error $ "get: descriptor unknown: " ++ show d
               ++ '\n' : show (map fst list)

getFromMap :: Descr -> Map.Map Descr a -> (Descr,a)
getFromMap d list =
  case Map.lookup d list of
    Just r -> (d, r)
    Nothing -> error $ "get: descriptor unknown: " ++ show d
               ++ '\n' : show (Map.keys list)

remove :: Eq a => a -> [(a, b)] -> [(a, b)]
remove x = filter ((x /=) . fst)

{- lookup a graph descriptor and execute a command on the graph
   the delete flag specifies if the graph should be removed from the graph
   list afterwards -}
fetchGraph :: Descr -> GraphInfo -> Bool -> ((AbstractionGraph, Descr)
            -> IO (AbstractionGraph, Descr, Descr, Maybe String)) -> IO Result
fetchGraph gid gv delete cmd = do
  (gs,ev_cnt) <- readIORef gv
  case lookup gid gs of
    Just g -> do
      (g',descr,ev_cnt',err) <- cmd (g,ev_cnt)
      let gs'' = if delete then gs' else (gid,g'):gs'
      writeIORef gv (gs'',ev_cnt')
      return (Result descr err)
      where gs' = remove gid gs
    Nothing -> return (Result 0 (Just ("Graph id "++show gid++" not found")))

getGraphid :: Descr -> GraphInfo -> IO OurGraph
getGraphid gid gv = do
  (gs,_) <- readIORef gv
  case lookup gid gs of
    Just g -> return $ theGraph g
    Nothing -> error "get_graphid: graph does not exist"

-- These are the operations of the interface

initgraphs :: IO GraphInfo
initgraphs =  newIORef ([],0)

makegraph :: String        -- Title
          -> Maybe (IO ()) -- FileOpen Menu
          -> Maybe (IO ()) -- FileSave Menu
          -> Maybe (IO ()) -- FileSaveAs Menu
          -> [GlobalMenu]
          -> [(String,DaVinciNodeTypeParms (String,Descr,Descr))]
          -> [(String,DaVinciArcTypeParms EdgeValue)] -> CompTable
          -> GraphInfo -> IO Result
makegraph title open save saveAs =
  makegraphExt title open save saveAs (return True) Nothing

makegraphExt :: String     -- Title
          -> Maybe (IO ()) -- FileOpen Menu
          -> Maybe (IO ()) -- FileSave Menu
          -> Maybe (IO ()) -- FileSaveAs Menu
          -> IO Bool       -- FileClose Menu
          -> Maybe (IO ()) -- FileExit Menu
          -> [GlobalMenu]
          -> [(String,DaVinciNodeTypeParms (String,Descr,Descr))]
          -> [(String,DaVinciArcTypeParms EdgeValue)] -> CompTable
          -> GraphInfo -> IO Result
makegraphExt title open save saveAs close exit menus nodetypeparams
             edgetypeparams comptable gv = do
  (gs,ev_cnt) <- readIORef gv
  let
    graphParms  =
      foldr ($$) (GraphTitle title $$
                  OptimiseLayout False $$
                  AllowClose close $$
                  FileMenuAct OpenMenuOption open $$
                  FileMenuAct SaveMenuOption save $$
                  FileMenuAct SaveAsMenuOption saveAs $$
                  FileMenuAct ExitMenuOption exit $$
                  emptyGraphParms)
                  menus
    abstractNodetypeparams =
      LocalMenu (
        Button "Unhide abstracted nodes"
          (\(_, descr, gid) -> do
             oldGv <- readIORef gv
             (Result _ error') <- showIt gid descr gv
             case error' of
               Just _ -> do
                 writeIORef gv oldGv
                 return ()
               Nothing -> do
                 redisplay gid gv
                 return ()
          )
        ) $$$
        Rhombus  $$$
        ValueTitle ( \ (name,_,_) -> return name) $$$
        emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)
    (nodetypenames,nodetypeparams1) =
      unzip (("ABSTRACT",abstractNodetypeparams):nodetypeparams)
    (edgetypenames,edgetypeparams1) = unzip edgetypeparams
    ontoGr = Graph.empty
    relViewSpecList = []
  graph <- newGraph graphtool graphParms
  nodetypes <- mapM (newNodeType graph) nodetypeparams1
  edgetypes <- mapM (newArcType graph) edgetypeparams1
  let g = AbstractionGraph {
            theGraph = graph,
            nodeTypes = zip nodetypenames nodetypes,
            edgeTypes = zip edgetypenames edgetypes,
            nodes = Map.empty,
            edges = Map.empty, -- [],
            edgeComp = comptable,
            eventTable = [],
            deletedNodes = [],
            hiddenEdges = [],
            ontoGraph = ontoGr,
            relViewSpecs = relViewSpecList,
            nodeMap = Map.empty }
  writeIORef gv ((ev_cnt,g):gs,ev_cnt+1)
  return (Result ev_cnt Nothing)

addnode :: Descr -> String -> String -> GraphInfo -> IO Result
addnode gid nodetype name gv =
  fetchGraph gid gv False (\ (g, ev_cnt) ->
------------------------------ why query nodetype first
    case lookup nodetype (nodeTypes g) of
      Nothing ->
        return (g,0,ev_cnt,Just ("addnode: illegal node type: "++nodetype))
      Just nt -> do
            node <- newNode (theGraph g) nt (name,ev_cnt,gid)
            return (g{nodes = Map.insert ev_cnt (nodetype,node) $ nodes g},
                    ev_cnt,ev_cnt+1,Nothing)
    )

{- | change the node type of the given node in the given graph.
     it firstly checks if the node exists in the graph and if
     the given node type is valid, then does the setting.
-}
changeNodeType :: Descr -- ^ the graph id
               -> Descr -- ^ the id of the to be set node
               -> String -- ^ the new node type
               -> GraphInfo -- ^ the enviroment
               -> IO Result
changeNodeType gid node nodetype graph =
  fetchGraph gid graph False (\(g, ev_cnt) ->
    case Map.lookup node (nodes g) of
      Nothing ->
        return (g, 0, ev_cnt, Just ("changeNodeType: illegal node: "
                                    ++ show node))
      Just n ->
        case lookup nodetype (nodeTypes g) of
          Nothing ->
            return (g, 0, ev_cnt,
                    Just ("changeNodeType: illegal node type: " ++ nodetype))
          Just nt -> do
            setNodeType (theGraph g) (snd n) nt
            let newnodes =
                   Map.mapWithKey
                   (\descr v@(_, davinciNode) -> if descr == node
                     then (nodetype, davinciNode) else v) $ nodes g
            return (g{nodes = newnodes}, node, ev_cnt+1, Nothing)
    )

writeOntoGraph :: Descr -> Tree.Gr (String,String,OntoObjectType) String
               -> GraphInfo -> IO Result
writeOntoGraph gid graph gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    return (g{ontoGraph = graph},0,ev_cnt+1,Nothing)
    )

writeRelViewSpecs :: Descr -> [RelationViewSpec] -> GraphInfo -> IO Result
writeRelViewSpecs gid specs gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    return (g{relViewSpecs = specs},0,ev_cnt+1,Nothing)
    )

writeNodeMap :: Descr -> NodeMapping -> GraphInfo -> IO Result
writeNodeMap gid nMap gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    return (g{nodeMap = nMap},0,ev_cnt+1,Nothing)
    )

delnode :: Descr -> Descr -> GraphInfo -> IO Result
delnode gid node gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    case Map.lookup node (nodes g) of
      Just n -> do
        deleteNode (theGraph g) (snd n)
        return (g{nodes = Map.delete node (nodes g)
                 ,deletedNodes = deletedNodes g},
                0,ev_cnt+1,Nothing)
      Nothing ->
        return (g,0,ev_cnt,Just ("delnode: illegal node: "++show node))
    )

addlink :: Descr -> String -> String -> Maybe (LEdge DGLinkLab) -> Descr
        -> Descr -> GraphInfo -> IO Result
addlink gid edgetype name label src tar gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    case (lookup edgetype (edgeTypes g),
          Map.lookup src (nodes g),
          Map.lookup tar (nodes g)) of
      (Just et, Just src_node, Just tar_node) -> do
        existingEdgesOfSameTypeAndPosition <-
          sequence [getArcValue (theGraph g) davinciArc
                    |(srcId, tgtId, tp, davinciArc) <- Map.elems (edges g),
                    tp == edgetype && srcId == src && tgtId == tar]
        case lookup name [(nm,descr)|(nm,descr,_) <-
          existingEdgesOfSameTypeAndPosition] of
           _ -> do
             edge <- newArc (theGraph g) et (name,ev_cnt,label) (snd src_node)
                       (snd tar_node)
             return (g{edges = Map.insert ev_cnt (src,tar,edgetype,edge)
                                          $ edges g},
                     ev_cnt,ev_cnt+1,Nothing)
      (Nothing,_,_) ->
        return (g,0,ev_cnt,Just ("addlink: illegal edge type: "++edgetype))
      (_,Nothing,_) ->
        return (g,0,ev_cnt,
                Just ("addlink: illegal source node id: "++show src))
      (_,_,Nothing) ->
        return (g,0,ev_cnt,
                Just ("addlink: illegal target node id: "++show tar))
    )

dellink :: Descr -> Descr -> GraphInfo -> IO Result
dellink gid edge gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    case Map.lookup edge (edges g) of
      Just (_,_,_,e) -> do
        deleteArc (theGraph g) e
        return (g{edges = Map.delete edge (edges g)},0,ev_cnt+1,Nothing)
      Nothing ->
        return (g,0,ev_cnt,Just ("dellink: illegal edge: "++show edge))
    )

redisplay :: Descr -> GraphInfo -> IO Result
redisplay gid gv =
  fetchGraph gid gv False (\(g,ev_cnt) -> do
    redraw (theGraph g)
    threadDelay delayTime
    return (g,0,ev_cnt+1,Nothing)
    )

{- determines from the types of two edges the type of the path replacing them
   (using the edgeComp table of the graph) -}
determineedgetype :: AbstractionGraph -> (String,String) -> Maybe String
determineedgetype g (t1,t2) =
  case [ t | (tp1, tp2, t) <- edgeComp g, tp1 == t1 && tp2 == t2 ] of
    [] -> Nothing
    x : _ -> Just x

{- returns a pair of lists: one list of all in- and one of all out-going edges
   of the node -}
fetchEdgesOfNode :: AbstractionGraph -> Descr -> Maybe ([Descr],[Descr])
fetchEdgesOfNode g node =
-- ? this checking seems meaningless...
--  case sequence (map ((flip Map.lookup) (edges g)) (Map.keys $ edges g)) of
  --  Just _ ->
      Just ([descr|(descr,(_,t,_,_)) <- Map.toList $ edges g, t == node],
            [descr|(descr,(s,_,_,_)) <- Map.toList $ edges g, s == node])
    --Nothing -> Nothing

hideSetOfNodeTypes :: Descr -> [String] -> Bool -> GraphInfo -> IO Result
hideSetOfNodeTypes gid nodetypes showLast gv =
  fetchGraph gid gv False (\ (g, ev_cnt) ->
    case mapM (flip lookup (nodeTypes g)) nodetypes of
      Just _ -> do
        let nodelist = [descr | (descr, (tp, _)) <- Map.toList (nodes g),
                        elem tp nodetypes && (not showLast || any
                          (\ (descr', _, _, _) -> descr' == descr)
                          (Map.elems $ edges g))]
        case nodelist of
          [] ->
            return (g,0,ev_cnt,Nothing)
          _ -> do
            (Result de error') <- hidenodes gid nodelist gv
            info <- readIORef gv
            return (snd (get gid (fst info)), de, (snd info), error')
      Nothing ->
        return (g,0,ev_cnt,Just ("hidenodetype: illegal node types "
                                 ++ "in list: " ++ showList nodetypes ","))
  )

hidenodes :: Descr -> [Descr] -> GraphInfo -> IO Result
hidenodes gid node_list gv =
  fetchGraph gid gv False (\ (g, ev_cnt) ->
    case mapM (flip Map.lookup (nodes g)) node_list of
      Just _ ->
        -- try to determine the path to add and the edges to remove
        case makepathsMain g node_list of
          -- try to create the paths
          Just (newEdges',delEdges) -> do
            -- save the old edges...
            let
              oeDescr = nub $ concatMap fst delEdges ++ concatMap snd delEdges
              oe = map (flip getFromMap (edges g)) oeDescr
            oldEdges' <- saveOldEdges g oe
            -- ... then try to remove them from the graph
            (gs,_) <- readIORef gv
            writeIORef gv (gs,ev_cnt+1)
            (Result _ error1) <- hideedgesaux gid oeDescr gv
            info1 <- readIORef gv
            case error1 of
              Nothing -> do
                -- determine the _new_ edges...
                let
                  existingEdges =
                    [(src,tgt,tp)|(src,tgt,tp,_) <-
                     Map.elems $ edges (snd (get gid (fst info1)))]
                  filteredNewEdges =
                    [path| path@(src,tgt,tp) <- newEdges',
                     notElem (src,tgt,tp) existingEdges]
                -- ... and try to add them
                (Result _ error2) <-
                  addpaths gid filteredNewEdges gv --info1
                case error2 of
                  Nothing -> do
                    -- save the old nodes...
                    let on = map (flip getFromMap (nodes g)) node_list
                    oldNodes' <- saveOldNodes g on
                    -- ... then try to remove them from the graph
                    (Result _ error3) <-
                      hidenodesaux gid node_list gv --info2
                    info3 <- readIORef gv
                    case error3 of
                      Nothing -> do
                        -- save the changes in an entry
                        let
                          g' = snd (get gid (fst info3))
                          newEdges'' = [edge| edge <- Map.toList (edges g'),
                                       Map.notMember (fst edge) (edges g)]
                          newEvent = createEntry [] oldNodes' newEdges''
                                       oldEdges' ev_cnt
                        return (g'{eventTable = newEvent : eventTable g'}
                               , ev_cnt, snd info3 + 1, Nothing)
                      Just t ->
                        return (g,0,ev_cnt,
                                Just ("hidenodes: error hiding nodes: "++t))
                  Just text ->
                    return (g,0,ev_cnt,
                            Just ("hidenodes: error adding paths: "++text))
              Just text ->
                return (g,0,ev_cnt,
                        Just ("hidenodes: error deleting edges: "++text))
          Nothing ->
            return (g,0,ev_cnt,
                    Just ("hidenodes: error making paths\n(possible reasons: "
                         ++"an error occured getting the edges of the nodes\n "
                         ++"or a pathtype could not be determined (missing "
                         ++"entry in edgeComp table))"))
      Nothing -> return (g,0,ev_cnt,Just "hidenodes: unknown node(s)")
    )

-- auxiliary function, which removes the nodes from the graph
hidenodesaux :: Descr -> [Descr] -> GraphInfo -> IO Result
hidenodesaux _ [] gv = do
  (_,ev_cnt) <- readIORef gv
  return (Result ev_cnt Nothing)
hidenodesaux gid (d:delNodes) gv = do
  deletedNode@(Result _ error') <- delnode gid d gv
  case error' of
    Nothing -> hidenodesaux gid delNodes gv
    Just _ -> return deletedNode

-- returns the paths to add and the edges to remove
makepathsMain :: AbstractionGraph -> [Descr]
              -> Maybe ([(Descr,Descr,String)],[([Descr],[Descr])])
makepathsMain g node_list =
  -- try to determine the in- and outgoing edges of the nodes
  case mapM (fetchEdgesOfNode g) node_list of
    -- try to make paths of these edges
    Just edgelistPairs ->
      case mapM (makepaths g node_list) edgelistPairs of
        -- the paths to add (dangling ones are removed) and the edges to remove
        Just paths ->
          Just (removeDanglingEdges (nub (concat paths)) node_list,
                edgelistPairs)
        Nothing -> Nothing
    Nothing -> Nothing

-- removes those edges whose source or target node will be hidden
removeDanglingEdges :: [(Descr,Descr,String)] -> [Descr]
                    -> [(Descr,Descr,String)]
removeDanglingEdges edges' nodes' =
  [edge| edge@(src,tgt,_) <- edges', notElem src nodes' && notElem tgt nodes']

-- returns a list of paths (ie source, target and type) to be added
makepaths :: AbstractionGraph ->  [Descr] -> ([Descr],[Descr])
          -> Maybe [(Descr,Descr,String)]
makepaths g node_list (inEdges,outEdges) =
  -- try to lookup the edges of the node
  case (mapM (flip Map.lookup (edges g)) inEdges,
        mapM (flip Map.lookup (edges g)) outEdges) of
    (Just ie, Just oe) ->
      -- try to make paths out of them
      case mapM (makepathsaux g node_list []) (specialzip ie oe) of
        -- return the paths
        Just paths -> Just (concat paths)
        Nothing -> Nothing
    (Nothing,_) -> Nothing
    (_,Nothing) -> Nothing

{- determines source, target and type of the path to be added and checks it
   using method checkpath -}
makepathsaux :: AbstractionGraph -> [Descr] -> [Descr]
             -> ((Descr,Descr,String,DaVinciArc EdgeValue),
                (Descr,Descr,String,DaVinciArc EdgeValue))
             -> Maybe [(Descr,Descr,String)]
makepathsaux g node_list alreadyPassedNodes ((s1,_,ty1,ed1),(_,t2,ty2,_)) =
  -- try to determine the type of the path
  case determineedgetype g (ty1,ty2) of
    -- return the checked path
    Just ty -> checkpath g node_list alreadyPassedNodes (s1,t2,ty,ed1)
               -- ed1 is just a dummy value (Dummiewert)
    Nothing -> Nothing

{- check, if the source or the target of an edge are element of the list of
   nodes that are to be hidden
   if so, find out the "next" sources/targets and check again
   remember which nodes have been passed to avoid infinite loops -}
checkpath :: AbstractionGraph -> [Descr] -> [Descr]
          -> (Descr,Descr,String,DaVinciArc EdgeValue)
          -> Maybe [(Descr,Descr,String)]
checkpath g node_list alreadyPassedNodes path@(src,tgt,ty,_)
  | elem src alreadyPassedNodes || elem tgt alreadyPassedNodes = Just []
  | elem src node_list =
    -- try to determine the in- and outgoing edges of the source node
    case fetchEdgesOfNode g src of
      -- try to lookup ingoing edges
      Just (inEdges,_) ->
        case mapM (flip Map.lookup (edges g)) inEdges of
          {- try to make paths of these edges and the "tail" of the path (and
             recursively check them) -}
          Just el ->
            case mapM (makepathsaux g node_list (src : alreadyPassedNodes))
              (specialzip el [path]) of
              Just p -> Just (concat p)
              Nothing -> Nothing
          Nothing -> Nothing
      Nothing -> Nothing
  | elem tgt node_list =
    -- try to determine the in- and outgoing edges of the target node
    case fetchEdgesOfNode g tgt of
      -- try to lookup the outgoing edges
      Just (_,outEdges) ->
        case mapM (flip Map.lookup (edges g)) outEdges of
          {- try to make paths of these edges and the "init" of the path (and
             recursively check them) -}
          Just el ->
            case mapM (makepathsaux g node_list
                                 (tgt : alreadyPassedNodes))
                          (specialzip [path] el) of
              Just p -> Just (concat p)
              Nothing -> Nothing
          Nothing -> Nothing
      Nothing -> Nothing
  | otherwise =
    -- nothing to be done
    Just [(src,tgt,ty)]

-- adds the paths (given source, target and type)
addpaths :: Descr -> [(Descr,Descr,String)] -> GraphInfo -> IO Result
addpaths _ [] gv = do
  (_,ev_cnt) <- readIORef gv
  return (Result ev_cnt Nothing)
addpaths gid ((src,tgt,ty):newEdges') gv = do
  edge@(Result _ error') <- addlink gid ty "" Nothing src tgt gv
  case error' of
    Nothing -> addpaths gid newEdges' gv
    Just _ -> return edge

hideSetOfEdgeTypes :: Descr -> [String] -> GraphInfo -> IO Result
hideSetOfEdgeTypes gid edgetypes gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    case sequence [lookup edgetype (edgeTypes g)|edgetype <- edgetypes] of
      Just _ -> do
        let edgelist = [descr| (descr, (_ ,_ , tp, _)) <- Map.toList (edges g),
                              elem tp edgetypes]
            showlist = filter (\ (_, (_, _, tp, _)) -> notElem tp edgetypes)
                              $ hiddenEdges g
        case edgelist of
          [] -> return (g, 0, ev_cnt, Nothing)
          _ -> do
            (Result de err) <- hideedges gid edgelist gv
            case err of
              Nothing -> do
                info <- readIORef gv
                let gs = (snd $ get de $ fst info)
                    gs' = gs{hiddenEdges = filter (flip notElem showlist)
                                           $ hiddenEdges gs}
                sl' <- saveOldEdges gs showlist
                writeIORef gv ((de + 1, gs') : fst info, de + 1)
                (Result de' err') <- showedges (de + 1) sl' gv
                case err' of
                  Nothing -> do
                    info' <- readIORef gv
                    return (snd $ get de' $ fst info', de', snd info', Nothing)
                  Just _ -> return (g, 0, ev_cnt, err')
              Just _ -> return (g, 0, ev_cnt, err)
      Nothing ->
        return (g, 0, ev_cnt, Just ("hideedgestype: illegal edge types "
                                    ++ "in list: " ++ showList edgetypes ","))
  )

hideedges :: Descr -> [Descr] -> GraphInfo -> IO Result
hideedges gid edge_list gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    case mapM (\ e -> case Map.lookup e (edges g) of
                                Just x -> Just (e,x)
                                Nothing -> Nothing) edge_list of
      Just edges' -> do
        Result de err <- hideedgesaux gid edge_list gv
        case err of
          Nothing -> do
            info <- readIORef gv
            return ((snd $ get gid $ fst info){hiddenEdges = hiddenEdges g
                                                             ++ edges'},
                    de, snd info + 1, Nothing)
          Just _ -> return (g,0,ev_cnt,Just "hideedges: error deleting edges")
      Nothing -> return (g,0,ev_cnt,Just "hideedges: unknown edge(s)")
  )

-- an auxiliary function, which removes the edges from the graph
hideedgesaux :: Descr -> [Descr] -> GraphInfo -> IO Result
hideedgesaux _ [] gv = do
  (_,ev_cnt) <- readIORef gv
  return (Result ev_cnt Nothing)
hideedgesaux gid (d:delEdges) gv = do
  dle@(Result _ error') <- dellink gid d gv
  case error' of
    Nothing -> hideedgesaux gid delEdges gv --info
    Just _ -> return dle

-- | function to check whether the internal nodes are hidden or not
checkHasHiddenNodes :: Descr -> Descr -> GraphInfo -> IO Result
checkHasHiddenNodes gid hide_event gv =
  fetchGraph gid gv False (\(g, ev_cnt) ->
    case lookup hide_event (eventTable g) of
      Just _ -> return (g, 0, ev_cnt, Nothing)
      Nothing -> return (g, 0, ev_cnt,
                         Just "checkHasHiddenNodes: hide events not found")
    )

-- function to undo hide-events
showIt :: Descr -> Descr -> GraphInfo -> IO Result
showIt gid hide_event gv =
  fetchGraph gid gv False (\(g,ev_cnt) ->
    -- try to lookup the hide-event
    case lookup hide_event (eventTable g) of
      Just entry -> do
        -- try to remove the paths that had been added
        (Result _ error1) <- hideedgesaux gid (map fst (newEdges entry)) gv
        case error1 of
          Nothing -> do
            -- try to add the nodes that had been hidden
            (Result _ error2) <- shownodes gid (oldNodes entry) gv
            case error2 of
              Nothing -> do
                -- try to remove the nodes that had been added
                (Result _ error3) <- hidenodesaux gid
                                         (map fst (newNodes entry)) gv
                case error3 of
                  Nothing -> do
                    -- try to add the edges that had been hidden
                    (Result _ error4) <- showedges gid (oldEdges entry) gv
                    info4 <- readIORef gv
                    case error4 of
                      Nothing -> do
                        -- remove the event from the eventTable
                        let g' = snd (get gid (fst info4))
                        return (g'{eventTable = remove hide_event
                                (eventTable g')},0,ev_cnt+1,Nothing)
                      Just t4 ->
                        return (g,0,ev_cnt,Just ("showIt: error restoring old "
                                                 ++"edges:\n-> "++t4))
                  Just t3 ->
                    return (g,0,ev_cnt,
                            Just ("showIt: error removing nodes:\n-> "++t3))
              Just t2 ->
                return (g,0,ev_cnt,Just ("showIt: error restoring nodes:\n-> "
                                         ++t2))
          Just t1 ->
            return (g,0,ev_cnt,Just ("showIt: error removing edges:\n-> "++t1))
      Nothing ->
        return (g,0,ev_cnt,Just ("showIt: invalid event descriptor: "
                                 ++ show hide_event))
    )

-- adds nodes that had been hidden
shownodes :: Descr -> [(Descr,(String,String))] -> GraphInfo -> IO Result
shownodes _ [] gv = do
  (_,ev_cnt) <- readIORef gv
  return (Result ev_cnt Nothing)
shownodes gid ((d,(tp,name)):list) gv = do
  (gs,_) <- readIORef gv
  -- try to add the first node
  writeIORef gv (gs,d)
  nd@(Result _ error') <- addnode gid tp name gv
  case error' of
    Nothing -> -- try to add the rest
      shownodes gid list gv
    Just _ -> return nd

-- adds edges that had been hidden
showedges :: Descr -> [(Int,(Int,Int,String,EdgeValue))] -> GraphInfo
          -> IO Result
showedges _ [] gv = do
  (_,ev_cnt) <- readIORef gv
  return (Result ev_cnt Nothing)
showedges gid ((d,(src,tgt,tp,value)):list) gv = do
  (gs,_) <- readIORef gv
  -- try to add the first edge
  writeIORef gv (gs,d)
  let
    name = getEdgeName value
    label = getEdgeLabel value
  ed@(Result _ err) <- addlink gid tp name label src tgt gv
  case err of
    Nothing -> -- try to add the rest
      showedges gid list gv
    Just _ -> return ed

{- | creates a list of the nodes that will be hidden (ie descriptor,type and
   name) -}
saveOldNodes :: AbstractionGraph
             -> [(Int,(String,DaVinciNode(String,Int,Int)))]
             -> IO [(Int,(String,String))]
saveOldNodes _ [] = return []
saveOldNodes g ((de,(tp,davincinode)):list) = do
  (name,_,_) <- getNodeValue (theGraph g) davincinode
  restOfList <- saveOldNodes g list
  return ((de,(tp,name)):restOfList)

{- | creates a list of the edges that will be hidden (ie descriptor,source,
   target,type and name) -}
saveOldEdges :: AbstractionGraph
             -> [(Int,(Int,Int,String,DaVinciArc EdgeValue))]
             -> IO [(Int,(Int,Int,String,EdgeValue))]
saveOldEdges _ [] = return []
saveOldEdges g ((de,(src,tgt,tp,davinciarc)):list) = do
  value <- getArcValue (theGraph g) davinciarc
  restOfList <- saveOldEdges g list
  return ((de,(src,tgt,tp,value)):restOfList)

getEdgeName :: EdgeValue -> String
getEdgeName (name,_,_) = name

getEdgeLabel :: EdgeValue -> Maybe (LEdge DGLinkLab)
getEdgeLabel (_,_,label) = label

-- | improve the layout of a graph like calling \"Layout->Improve All\"
layoutImproveAll :: Descr -> GraphInfo -> IO Result
layoutImproveAll gid gv =
    fetchGraph gid gv False (\(g,ev_cnt) -> do
             let contxt = case theGraph g of
                            Graph dg -> getDaVinciGraphContext dg
             doInContext (DVT.Menu $ DVT.Layout DVT.ImproveAll) contxt
             return (g,0,ev_cnt+1,Nothing))

-- | display a message in a uDrawGraph window controlled by AbstractGraphView
showTemporaryMessage :: Descr -> GraphInfo
                     -> String -- ^ message to be displayed
                     -> IO Result
showTemporaryMessage gid gv message =
    fetchGraph gid gv False (\(g,ev_cnt) -> do
             let contxt = case theGraph g of
                            Graph dg -> getDaVinciGraphContext dg
             doInContext (DVT.Window $ DVT.ShowMessage message) contxt
             return (g,0,ev_cnt+1,Nothing))

-- | deactivate the input of all uDrawGraph windows;
--
-- Warning: every deactivate event must be paired an activate event
deactivateGraphWindow :: Descr -> GraphInfo -> IO Result
deactivateGraphWindow gid gv =
    fetchGraph gid gv False (\(g,ev_cnt) -> do
             let contxt = case theGraph g of
                            Graph dg -> getDaVinciGraphContext dg
             doInContext (DVT.Window DVT.Deactivate) contxt
             return (g,0,ev_cnt+1,Nothing))

-- | activate the input of a uDrawGraph display
activateGraphWindow :: Descr -> GraphInfo -> IO Result
activateGraphWindow gid gv =
    fetchGraph gid gv False (\(g,ev_cnt) -> do
             let contxt = case theGraph g of
                            Graph dg -> getDaVinciGraphContext dg
             doInContext (DVT.Window DVT.Activate) contxt
             return (g,0,ev_cnt+1,Nothing))
