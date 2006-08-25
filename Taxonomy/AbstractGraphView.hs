{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable (uni)

Interface for graph viewing and abstraction.
   It is possible to hide sets of nodes and edges.
   Using a composition table for edge types,
   paths through hidden nodes can be displayed.
   Graphs, nodes, and edges are handled via
   descriptors (here: integers), while node and
   edge types are handled by user-supplied strings.
-}

module Taxonomy.AbstractGraphView where

import DaVinciGraph
import Computation
import GraphDisp
import GraphConfigure
import Destructible

import Data.List(nub)
import Data.IORef

import Taxonomy.MMiSSOntology

import qualified Data.Graph.Inductive.Graph as Graph
import Common.Lib.Graph as Tree
import qualified Common.Lib.Map as Map

{- methods using fetch_graph return a quadruple containing the modified graph, a descriptor of the last modification (e.g. a new node), the descriptor that can be used for the next modification and a possible error message-}

-- Which graph display tool to be used, perhaps make it more tool independent?

instance Eq (DaVinciNode a) where
    (==) = eq1

instance Eq (DaVinciArc a) where
    (==) = eq1


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
data AbstractionGraph = AbstractionGraph {
       ontoGraph :: Tree.Gr (String,String,OntoObjectType) String,
       relViewSpecs :: [RelationViewSpec],
       nodeMap :: NodeMapping,
       theGraph :: OurGraph,
       nodeTypes :: [(String,DaVinciNodeType (String,Int,Int))],
       edgeTypes :: [(String,DaVinciArcType (String,Int))],
       nodes :: [(Int,(String,DaVinciNode (String,Int,Int)))],
       edges :: [(Int,(Int,Int,String,DaVinciArc (String,Int)))],
       -- probably, also the abstracted graph needs to be stored,
       -- and a list of hide/abstract events with the hidden nodes/edges (for each event),
       -- which is used to restore things when showIt is called
       edgeComp :: CompTable,
       eventTable :: [(Int,Entry)]}

type NodeMapping = Map.Map Int Descr

type Descr = Int
type GraphInfo = IORef ([(Descr,AbstractionGraph)],Descr) -- for each graph the descriptor and the graph,
                                                         -- plus a global counter for new descriptors
data Result = Result Descr                          -- graph, node or edge descriptor
                     (Maybe String)                 -- a possible error message


data Entry = Entry {newNodes :: [(Descr,(String,DaVinciNode (String,Int,Int)))],
                    oldNodes :: [(Descr,(String,String))],
                    newEdges :: [(Int,(Int,Int,String,DaVinciArc (String,Int)))],
                    oldEdges :: [(Int,(Int,Int,String,String))]
                    }

data RelationViewSpec = RelViewSpec String Bool Bool


-- creates a new entry of the eventTable and fills it with the data contained in its parameters
createEntry :: [(Descr,(String,DaVinciNode (String,Int,Int)))] -> [(Descr,(String,String))] -> [(Descr,(Int,Int,String,DaVinciArc (String,Int)))] -> [(Descr,(Int,Int,String,String))] -> Descr -> (Int,Entry)
createEntry nn on ne oe cnt = (cnt, Entry {newNodes = nn, oldNodes = on, newEdges = ne, oldEdges = oe})


-- zips two lists by pairing each element of the first with each element of the second
specialzip :: [a] -> [b] -> [(a,b)]
specialzip [] _ = []
specialzip _ [] = []
specialzip (x:xs) (y:ys) = (x,y):(specialzip [x] ys)++(specialzip xs (y:ys))


-- similar to lookup, but also returns the decriptor
-- should only be used, if lookup will be successful (otherwise an error is thrown)
get :: Descr -> [(Descr,a)] -> (Descr,a)
get d list = case lookup d list of
                Just r -> (d,r)
                Nothing -> error ("get: descriptor unknown: "++(show d)++"\n"++(show (map fst list)))


-- lookup tables and failure handling

remove :: Eq a => a -> [(a,b)] -> [(a,b)]
remove x l = filter (\(y,_) -> not (x==y)) l


return_fail graphs msg =
  return (Result 0 (Just msg))

-- lookup a graph descriptor and execute a command on the graph
-- the delete flag specifies if the graph should be removed from the graph list afterwards
-- fetch_graph :: Descr -> GraphInfo -> Bool -> a ?
fetch_graph gid gv delete cmd =
  do (gs,ev_cnt) <- readIORef gv
     case lookup gid gs of
       Just g -> do (g',descr,ev_cnt',err) <- cmd (g,ev_cnt)
                    let gs'' = if delete then gs' else (gid,g'):gs'
                    writeIORef gv (gs'',ev_cnt')
                    return (Result descr err)
                    where gs' = remove gid gs
       Nothing -> return (Result 0 (Just ("Graph id "++show gid++" not found")))


-- These are the operations of the interface

get_graphid :: Descr -> GraphInfo -> IO OurGraph
get_graphid gid gv = do
  (gs,ev_cnt) <- readIORef gv
  case lookup gid gs of
       Just g -> return $ theGraph g
       Nothing -> error "get_graphid: graph does not exist"


initgraphs :: IO GraphInfo
initgraphs = do newRef <- newIORef ([],0)
                return newRef

makegraph :: String -> [GlobalMenu] ->
             [(String,DaVinciNodeTypeParms (String,Descr,Descr))] ->
             [(String,DaVinciArcTypeParms (String,Descr))] ->
             CompTable -> GraphInfo -> IO Result
makegraph title menus nodetypeparams edgetypeparams comptable gv = do
  (gs,ev_cnt) <- readIORef gv
  let graphParms  =
       foldr ($$) (GraphTitle title $$
                   OptimiseLayout True $$
                   AllowClose (return True) $$
                   emptyGraphParms)
                   menus
      abstractNodetypeparams = LocalMenu
                                  (
                                      Button "Unhide abstracted nodes" (
                                        \ (name, descr, gid) -> do oldGv <- readIORef gv
                                                                   (Result descr error) <- showIt gid descr gv
                                                                   case error of
                                                                     Just _ -> do writeIORef gv oldGv
                                                                                  return ()
                                                                     Nothing -> do redisplay gid gv
                                                                                   return ()
                                         )
                                      ) $$$
                               Rhombus  $$$
                               ValueTitle ( \ (name,descr,gid) -> return name) $$$
                               emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)
      (nodetypenames,nodetypeparams1) = unzip (("ABSTRACT",abstractNodetypeparams):nodetypeparams)
      (edgetypenames,edgetypeparams1) = unzip edgetypeparams
  graph <- GraphDisp.newGraph graphtool graphParms
  ontoGr <- return(Graph.empty)
  relViewSpecList <- return([])
  nodetypes <- sequence (map (newNodeType graph) nodetypeparams1)
  edgetypes <- sequence (map (newArcType graph) edgetypeparams1)
  let g = AbstractionGraph {
            ontoGraph = ontoGr,
            relViewSpecs = relViewSpecList,
            nodeMap = Map.empty,
            theGraph = graph,
            nodeTypes = zip nodetypenames nodetypes,
            edgeTypes = zip edgetypenames edgetypes,
            nodes = [],
            edges = [],
            edgeComp = comptable,
            eventTable = [] }
  writeIORef gv ((ev_cnt,g):gs,ev_cnt+1)
  return (Result ev_cnt Nothing)

delgraph :: Descr -> GraphInfo -> IO Result
delgraph gid gv =
  fetch_graph gid gv True
   (\(g,ev_cnt) -> do destroy (theGraph g)
                      return (g,0,ev_cnt+1,Nothing))


delallgraphs :: GraphInfo -> IO ()
delallgraphs gv = do
  (gs,ev_cnt) <- readIORef gv
  destroy_all gs ev_cnt
  where
    destroy_all [] _ = return ()
    destroy_all ((gid,_):gs) ev_cnt = do
         writeIORef gv (gs,ev_cnt)
         Result _ _ <- Taxonomy.AbstractGraphView.delgraph gid gv
         (_,ev_cnt') <- readIORef gv
         destroy_all gs ev_cnt'

addnode :: Descr -> String -> String -> GraphInfo -> IO Result
addnode gid nodetype name gv =
   fetch_graph gid gv False (\(g,ev_cnt) ->
      do case lookup nodetype (nodeTypes g) of
          Nothing -> return (g,0,ev_cnt,Just ("addnode: illegal node type: "++nodetype))
          Just nt ->
            do existingNodesOfSameType <- sequence [(getNodeValue (theGraph g) davinciNode)|(descr,(tp,davinciNode)) <- (nodes g), tp == nodetype]
               case elem name [existingName| (existingName, _,_) <- existingNodesOfSameType] of
                 False -> do node <- newNode (theGraph g) nt (name,ev_cnt,gid)
                             return (g{nodes = (ev_cnt,(nodetype,node)):nodes g},ev_cnt,ev_cnt+1,Nothing)
                 True -> do return (g,0,ev_cnt, Just("addnode: node \"" ++ name ++ "\" of type " ++ nodetype ++ " already exists in graph " ++ (show gid)))
   )


writeOntoGraph :: Descr -> Tree.Gr (String,String,OntoObjectType) String
               -> GraphInfo -> IO Result
writeOntoGraph gid graph gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    return (g{ontoGraph = graph},0,ev_cnt+1,Nothing)
  )

writeRelViewSpecs :: Descr -> [RelationViewSpec] -> GraphInfo -> IO Result
writeRelViewSpecs gid specs gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    return (g{relViewSpecs = specs},0,ev_cnt+1,Nothing)
  )


writeNodeMap :: Descr -> NodeMapping -> GraphInfo -> IO Result
writeNodeMap gid nMap gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    return (g{nodeMap = nMap},0,ev_cnt+1,Nothing)
  )


delnode :: Descr -> Descr -> GraphInfo -> IO Result
delnode gid node gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
      case lookup node (nodes g) of
        Just n -> do deleteNode (theGraph g) (snd n)
                     return (g{nodes = remove node (nodes g)},0,ev_cnt+1,Nothing)
        Nothing ->  return (g,0,ev_cnt,Just ("delnode: illegal node: "++show node))
    )
{-
changenodetype
unclear how to implement, ask George
-}

addlink :: Descr -> String -> String -> Descr -> Descr -> GraphInfo -> IO Result
addlink gid edgetype name src tar gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    case (lookup edgetype (edgeTypes g),
          lookup src (nodes g),
          lookup tar (nodes g)) of
    (Just et, Just src_node, Just tar_node) ->
      do existingEdgesOfSameTypeAndPosition <- sequence [(getArcValue (theGraph g) davinciArc)|(descr,(srcId, tgtId, tp, davinciArc)) <- (edges g), tp == edgetype && srcId == src && tgtId == tar]
         case lookup name existingEdgesOfSameTypeAndPosition of
           Nothing ->
             do edge <- newArc (theGraph g) et (name,ev_cnt) (snd src_node) (snd tar_node)
                return (g{edges = (ev_cnt,(src,tar,edgetype,edge)):edges g},ev_cnt,ev_cnt+1,Nothing)
           Just _ -> do srcToString <- getNodeNameAndTypeAsString g src
                        tarToString <- getNodeNameAndTypeAsString g tar
                        return (g,0,ev_cnt,Just("addlink: edge \""++name++"\" from node "++(show src)++(srcToString)++" to node "++(show tar)++(tarToString)++" of type "++edgetype++" already exists in graph "++(show gid)))
    (Nothing,_,_) -> return (g,0,ev_cnt,Just ("addlink: illegal edge type: "++edgetype))
    (_,Nothing,_) -> return (g,0,ev_cnt,Just ("addlink: illegal source node id: "++show src))
    (_,_,Nothing) -> return (g,0,ev_cnt,Just ("addlink: illegal target node id: "++show tar))
   )


getNodeNameAndTypeAsString :: AbstractionGraph -> Descr -> IO String
getNodeNameAndTypeAsString g descr = case lookup descr (nodes g) of
                                        Just (tp, davinciNode) ->
                                          do (name, i, j) <- getNodeValue (theGraph g) davinciNode
                                             return (" (\""++name++"\" of type "++tp++")")
                                        Nothing -> error ("getNodeNameAndTypeAsString: unknown node: "++(show descr))


dellink :: Descr -> Descr -> GraphInfo -> IO Result
dellink gid edge gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    case lookup edge (edges g) of
        Just (_,_,_,e) ->
           do deleteArc (theGraph g) e
              return (g{edges = remove edge (edges g)},0,ev_cnt+1,Nothing)
        Nothing -> return (g,0,ev_cnt,Just ("dellink: illegal edge: "++show edge))
   )

redisplay :: Descr -> GraphInfo -> IO Result
redisplay gid gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    do redraw (theGraph g)
       return (g,0,ev_cnt+1,Nothing)
    )

-- determines from the types of two edges the type of the path replacing them (using the edgeComp table of the graph)
determineedgetype :: AbstractionGraph -> (String,String) -> Maybe String
determineedgetype g (t1,t2) =
  let result = [t | (tp1,tp2,t) <- (edgeComp g), ((tp1==t1)&&(tp2==t2))]
  in case result of
       [] -> Nothing
       x:xs -> Just x

-- returns a pair of lists: one list of all in- and one of all out-going edges of the node
fetchEdgesOfNode :: AbstractionGraph -> Descr -> Maybe ([Descr],[Descr])
fetchEdgesOfNode g node = case sequence (map ((flip lookup) (edges g)) (map fst (edges g))) of
                            Just el -> Just ([descr|ed@(descr,(_,t,_,_)) <- (edges g), t == node],[descr|ed@(descr,(s,_,_,_)) <- (edges g), s == node])
                            Nothing -> Nothing


hidenodes :: Descr -> [Descr] -> GraphInfo -> IO Result
hidenodes gid node_list gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    case sequence (map (\node -> lookup node (nodes g)) node_list) of
      Just nl -> do -- try to determine the path to add and the edges to remove
                    case makepathsMain g node_list of
                    -- try to create the paths
                      Just (newEdges,delEdges) -> do -- save the old edges...
                                                     let oeDescr = nub ((concat (map fst delEdges))++(concat (map snd delEdges)))
                                                         oe = map (\ed -> get ed (edges g)) oeDescr
                                                     oldEdges <- saveOldEdges g oe
                                                     -- ... then try to remove them from the graph
                                                     (gs,_) <- readIORef gv
                                                     writeIORef gv (gs,ev_cnt+1)
                                                     deletedEdges@(Result de1 error1) <- hideedgesaux gid oeDescr gv
                                                     info1 <- readIORef gv
                                                     case error1 of
                                                       Nothing -> do -- determine the _new_ edges...
                                                                     let existingEdges = [(src,tgt,tp)|(descr,(src,tgt,tp,daVinci)) <- (edges (snd (get gid (fst info1))))]
                                                                         filteredNewEdges = [path| path@(src,tgt,tp) <- newEdges, notElem (src,tgt,tp) existingEdges]
                                                                     -- ... and try to add them
                                                                     paths@(Result de2 error2) <- addpaths gid filteredNewEdges gv --info1
                                                                     case error2 of
                                                                       Nothing -> do -- save the old nodes...
                                                                                     let on = map (\nd -> get nd (nodes g)) node_list
                                                                                     oldNodes <- saveOldNodes g on
                                                                                     -- ... then try to remove them from the graph
                                                                                     deletedNodes@(Result de3 error3) <- hidenodesaux gid node_list gv --info2
                                                                                     info3 <- readIORef gv
                                                                                     case error3 of
                                                                                       Nothing -> do -- save the changes in an entry
                                                                                                     let g' = snd (get gid (fst info3))
                                                                                                         newEdges = [edge| edge <- (edges g'), notElem edge (edges g)]
                                                                                                         newEvent = createEntry [] oldNodes newEdges oldEdges ev_cnt
                                                                                                     return (g'{eventTable = newEvent:eventTable g'},ev_cnt,(snd info3)+1,Nothing)
                                                                                       Just t -> return (g,0,ev_cnt,Just ("hidenodes: error hiding nodes: "++t))
                                                                       Just text -> return (g,0,ev_cnt,Just ("hidenodes: error adding paths: "++text))
                                                       Just text -> return (g,0,ev_cnt,Just ("hidenodes: error deleting edges: "++text))
                      Nothing -> return (g,0,ev_cnt,Just "hidenodes: error making paths\n(possible reasons: an error occured getting the edges of the nodes\nor a pathtype could not be determined (missing entry in edgeComp table))")
      Nothing -> return (g,0,ev_cnt,Just "hidenodes: unknown node(s)")
  )


-- auxiliary function, which removes the nodes from the graph
hidenodesaux :: Descr -> [Descr] -> GraphInfo -> IO Result
hidenodesaux gid [] gv = do (gs,ev_cnt) <- readIORef gv
                            return (Result ev_cnt Nothing)
hidenodesaux gid (d:delNodes) gv = do deletedNode@(Result de error) <- delnode gid d gv
                                      case error of
                                        Nothing -> do hidenodesaux gid delNodes gv
                                        Just t -> return deletedNode


-- returns the paths to add and the edges to remove
makepathsMain :: AbstractionGraph -> [Descr] -> Maybe ([(Descr,Descr,String)],[([Descr],[Descr])])
makepathsMain g node_list =
  -- try to determine the in- and outgoing edges of the nodes
  case sequence (map (fetchEdgesOfNode g) node_list) of
     -- try to make paths of these edges
     Just edgelistPairs -> case sequence (map (makepaths g node_list) edgelistPairs) of
                                         -- return the paths to add and the edges to remove
                                         Just paths -> Just (nub (concat paths),edgelistPairs)
                                         Nothing -> Nothing
     Nothing -> Nothing


-- returns a list of paths (ie source, target and type) to be added
makepaths :: AbstractionGraph ->  [Descr] -> ([Descr],[Descr]) -> Maybe [(Descr,Descr,String)]
makepaths g node_list (inEdges,outEdges) =
  -- try to lookup the edges of the node
  case (sequence (map (\ed -> lookup ed (edges g)) inEdges),sequence (map (\ed -> lookup ed (edges g)) outEdges)) of
    (Just ie, Just oe) ->
       -- try to make paths out of them
       case sequence (map (makepathsaux g node_list []) (specialzip ie oe)) of
          -- return the paths
          Just paths -> Just (concat paths)
          Nothing -> Nothing
    (Nothing,_) -> Nothing
    (_,Nothing) -> Nothing


-- determines source, target and type of the path to be added and checks it using method checkpath
makepathsaux :: AbstractionGraph -> [Descr] -> [Descr] -> ((Descr,Descr,String,DaVinciArc(String,Int)),(Descr,Descr,String,DaVinciArc(String,Int))) -> Maybe [(Descr,Descr,String)]
makepathsaux g node_list alreadyPassedNodes ((s1,t1,ty1,ed1),(s2,t2,ty2,ed2)) =
  -- try to determine the type of the path
  case determineedgetype g (ty1,ty2) of
    -- return the checked path
    Just ty -> checkpath g node_list alreadyPassedNodes (s1,t2,ty,ed1)  -- ed1 is just a dummy value (Dummiewert)
    Nothing -> Nothing


-- check, if the source or the target of an edge are element of the list of nodes that are to be hidden
-- if so, find out the "next" sources/targets and check again
-- remember which nodes have been passed to avoid infinite loops
checkpath :: AbstractionGraph -> [Descr] -> [Descr] -> (Descr,Descr,String,DaVinciArc(String,Int)) -> Maybe [(Descr,Descr,String)]
checkpath g node_list alreadyPassedNodes path@(src,tgt,ty,ed)
  | elem src alreadyPassedNodes || elem tgt alreadyPassedNodes = Just []
  | elem src node_list = -- try to determine the in- and outgoing edges of the source node
                         case fetchEdgesOfNode g src of
                           -- try to lookup ingoing edges
                           Just (inEdges,outEdges) -> case sequence (map (\ed -> lookup ed (edges g)) inEdges) of
                                                        -- try to make paths of these edges and the "tail" of the path (and recursively check them)
                                                        Just el -> case sequence (map (makepathsaux g node_list (src:alreadyPassedNodes)) (specialzip el [path])) of
                                                                     Just p -> Just (concat p)
                                                                     Nothing -> Nothing
                                                        Nothing -> Nothing

  | elem tgt node_list = -- try to determine the in- and outgoing edges of the target node
                         case fetchEdgesOfNode g tgt of
                           -- try to lookup the outgoing edges
                           Just (inEdges,outEdges) -> case sequence (map (\ed -> lookup ed (edges g)) outEdges) of
                                                        -- try to make paths of these edges and the "init" of the path (and recursively check them)
                                                        Just el -> case sequence (map (makepathsaux g node_list (tgt:alreadyPassedNodes)) (specialzip [path] el)) of
                                                                     Just p -> Just (concat p)
                                                                     Nothing -> Nothing
                                                        Nothing -> Nothing
                           Nothing -> Nothing
  | otherwise = -- nothing to be done
                Just [(src,tgt,ty)]


-- adds the paths (given source, target and type)
addpaths :: Descr -> [(Descr,Descr,String)] -> GraphInfo -> IO Result
addpaths gid [] gv = do (gs,ev_cnt) <- readIORef gv
                        return (Result ev_cnt Nothing)
addpaths gid ((src,tgt,ty):newEdges) gv = do edge@(Result de error) <- addlink gid ty "" src tgt gv
                                             case error of
                                               Nothing -> do addpaths gid newEdges gv
                                               Just t -> return edge


-- fetches all the nodes of the given type and hides them using hidenodes
hidenodetype :: Descr -> String -> GraphInfo -> IO Result
hidenodetype gid nodetype gv = fetch_graph gid gv False (\(g,ev_cnt) ->
                                           -- check if the node type is valid
                                           do case lookup nodetype (nodeTypes g) of
                                               Just nt ->
                                                 do let nodelist = [descr|(descr,(tp,_)) <- (nodes g), tp == nodetype]
                                                    case nodelist of
                                                      [] -> do return (g,0,ev_cnt,Just ("hidenodetype: no nodes of type "++nodetype++" found in graph "++(show gid)))
                                                      node_list -> do (Result de error) <- hidenodes gid nodelist gv
                                                                      info <- readIORef gv
                                                                      return (snd (get gid (fst info)), de, (snd info), error)
                                               Nothing -> return (g,0,ev_cnt,Just ("hidenodetype: illegal node type: "++nodetype))

                                        )


-- like hidenodes, but replaces the hidden nodes by a new node
-- with a menu to unhide the nodes (not yet implemented)
abstractnodes :: Descr -> [Descr] -> GraphInfo -> IO Result
abstractnodes gid [] gv = fetch_graph gid gv False (\(g,ev_cnt) -> return (g,0,ev_cnt,Nothing))
abstractnodes gid node_list gv =
    fetch_graph gid gv False (\(g,ev_cnt) ->
      -- try to lookup the nodes of the list
      case sequence (map (\nd -> lookup nd (nodes g)) node_list) of
        Just nl -> -- try to lookup the in- and outgoing edges of the nodes
                   case sequence (map (fetchEdgesOfNode g) node_list) of
                     Just el -> do -- save the old edges
                                   let oeDescr = nub ((concat (map fst el))++(concat (map snd el)))
                                       oe = map (\edge -> get edge (edges g)) oeDescr
                                   oldEdges <- saveOldEdges g oe
                                   -- save the old nodes
                                   let on = map (\node -> get node (nodes g)) node_list
                                   oldNodes <- saveOldNodes g on
                                   -- try to create the new abstract node and add its in- and outgoing paths
                                   (Result de1 error1) <- replaceByAbstractNode gid node_list nl oeDescr gv --(gs,ev_cnt+1)
                                   case error1 of
                                     Nothing -> do -- try to remove the in- and outgoing edges of the nodes to be hidden
                                                   (Result de2 error2) <- hideedgesaux gid oeDescr gv
                                                   case error2 of
                                                     Nothing -> do -- try to remove the nodes of the list
                                                                   (Result de3 error3) <- hidenodesaux gid node_list gv --info2
                                                                   info3 <- readIORef gv
                                                                   case error3 of
                                                                     Nothing -> do -- save the changes in an entry
                                                                                   let g' = snd (get gid (fst info3))
                                                                                       newNodes = [nd| nd <- nodes g', notElem nd (nodes g)]
                                                                                       newEdges = [ed| ed <- edges g', notElem ed (edges g)]
                                                                                       newEntry = createEntry newNodes oldNodes newEdges oldEdges ev_cnt
                                                                                   return (g'{eventTable=newEntry:eventTable g'},ev_cnt,snd info3,Nothing)
                                                                     Just t -> return (g,0,ev_cnt,Just ("abstractnodes: error hiding nodes: "++t))
                                                     Just t -> return (g,0,ev_cnt,Just ("abstractnodes: error hiding edges: " ++ t))
                                     Just t -> return (g,0,ev_cnt,Just ("abstractnodes: error making abstract node: "++ t))
                     Nothing -> return (g,0,ev_cnt,Just "abstractnodes: error fetching the edges of the nodes")
        Nothing -> return (g,0,ev_cnt,Just "abstractnodes: unknown nodes")
    )


-- adds an abstract node, determines and adds its in- and outgoing paths
replaceByAbstractNode :: Descr -> [Descr] -> [(String,DaVinciNode(String,Int,Int))] -> [Descr] -> GraphInfo -> IO Result
replaceByAbstractNode gid node_list nl edge_list gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    -- try to lookup the in- and outgoing edges of the nodes that are to be hidden
    case sequence (map (\ed -> lookup ed (edges g)) edge_list) of
      Just el -> do -- try to add an abstract node
                    (Result de1 error1) <- addnode gid "ABSTRACT" (show ev_cnt) gv
                    case error1 of
                      Nothing -> do -- determine its in- and outgoing paths...
                                    let newEdges = [(src,de1,tp)| (src,tgt,tp,_) <- el, ((notElem src node_list) && (elem tgt node_list))]
                                                     ++ [(de1,tgt,tp)| (src,tgt,tp,_) <- el, ((elem src node_list) && (notElem tgt node_list))]
                                    -- ... and try to add them
                                    (Result de2 error2) <- addpaths gid (nub newEdges) gv
                                    info2 <- readIORef gv
                                    case error2 of
                                      Nothing -> do -- return the modified graph
                                                    let g' = snd (get gid (fst info2))
                                                    return (g',de2,snd info2,Nothing)
                                      Just t -> return (g,0,ev_cnt,error2)
                      Just text -> return (g,0,ev_cnt,Just ("replaceByAbstractNode: error creating abstract node: "++text))
      Nothing -> return (g,0,ev_cnt,Just "replaceByAbstractNode: error looking up the edges of the nodes")
  )


hideedges :: Descr -> [Descr] -> GraphInfo -> IO Result
hideedges gid edge_list gv = fetch_graph gid gv False (\(g,ev_cnt) ->
                                        -- check if all of the edges exist
                                        case sequence (map (\edge -> lookup edge (edges g)) edge_list) of
                                           Just el -> do -- save the old edges ...
                                                         let oe = map (\edge -> get edge (edges g)) edge_list
                                                         oldEdges <- saveOldEdges g oe
                                                         -- ... then try to remove them from the graph
                                                         (gs,_) <- readIORef gv
                                                         writeIORef gv (gs,ev_cnt+1)
                                                         (Result de error) <- hideedgesaux gid edge_list gv
                                                         info <- readIORef gv
                                                         case error of
                                                           Nothing -> do -- save the changes in an entry
                                                                         let g' = snd (get gid (fst info))
                                                                             newEntry = createEntry [] [] [] oldEdges ev_cnt
                                                                         return (g'{eventTable = newEntry:eventTable g'},ev_cnt,snd info,Nothing)
                                                           Just text -> return (g,0,ev_cnt,Just ("hideedges: error hiding edges: "++text))
                                           Nothing -> return (g,0,ev_cnt,Just "hideedges: unknown edges")
                                      )

-- an auxiliary function, which removes the edges from the graph
hideedgesaux :: Descr -> [Descr] -> GraphInfo -> IO Result
hideedgesaux gid [] gv = do (gs,ev_cnt) <- readIORef gv
                            return (Result ev_cnt Nothing)
hideedgesaux gid (d:delEdges) gv = do dle@(Result descr error) <- dellink gid d gv
                                      case error of
                                        Nothing -> do hideedgesaux gid delEdges gv --info
                                        Just t -> return dle


-- fetches all the edges of the given type and hides them using hideedges
hideedgetype :: Descr -> String -> GraphInfo -> IO Result
hideedgetype gid edgetype gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    -- check if the edge type is valid
    case lookup edgetype (edgeTypes g) of
      Just et -> do let edgelist = [descr|(descr,(_,_,tp,_)) <- (edges g), tp == edgetype]
                    case edgelist of
                      [] -> do return (g,0,ev_cnt,Just ("hideedgetype: no edges of type "++edgetype++" found in graph "++(show gid)))
                      edge_list -> do (Result de error) <- hideedges gid edge_list gv
                                      info <- readIORef gv
                                      return (snd (get gid (fst info)), de, snd info,error)
      Nothing -> return (g,0,ev_cnt,Just ("hideedgetype: illegal edge type: "++edgetype))
  )


-- function to undo hide-events
showIt :: Descr -> Descr -> GraphInfo -> IO Result
showIt gid hide_event gv =
  fetch_graph gid gv False (\(g,ev_cnt) ->
    -- try to lookup the hide-event
    case lookup hide_event (eventTable g) of
      Just entry -> do -- try to remove the paths that had been added
                       (Result de1 error1) <- hideedgesaux gid (map fst (newEdges entry)) gv
                       case error1 of
                         Nothing -> do -- try to add the nodes that had been hidden
                                       (Result de2 error2) <- shownodes gid (oldNodes entry) gv
                                       case error2 of
                                         Nothing -> do -- try to remove the nodes that had been added
                                                       (Result de3 error3) <- hidenodesaux gid (map fst (newNodes entry)) gv
                                                       case error3 of
                                                         Nothing -> do -- try to add the edges that had been hidden
                                                                       (Result de4 error4) <- showedges gid (oldEdges entry) gv
                                                                       info4 <- readIORef gv
                                                                       case error4 of
                                                                         Nothing -> do -- remove the event from the eventTable
                                                                                       let g' = snd (get gid (fst info4))
                                                                                       return (g'{eventTable = remove hide_event (eventTable g')},0,ev_cnt+1,Nothing)
                                                                         Just t4 -> return (g,0,ev_cnt,Just ("showIt: error restoring old edges:\n-> "++t4))
                                                         Just t3 -> return (g,0,ev_cnt,Just ("showIt: error removing nodes:\n-> "++t3))
                                         Just t2 -> return (g,0,ev_cnt,Just ("showIt: error restoring nodes:\n-> "++t2))
                         Just t1 -> return (g,0,ev_cnt,Just ("showIt: error removing edges:\n-> "++t1))
      Nothing -> return (g,0,ev_cnt,Just ("showIt: invalid event descriptor: "++(show hide_event)))
  )



-- adds nodes that had been hidden
shownodes :: Descr -> [(Descr,(String,String))] -> GraphInfo -> IO Result
shownodes gid [] gv = do (gs,ev_cnt) <- readIORef gv
                         return (Result ev_cnt Nothing)
shownodes gid ((node@(d,(tp,name))):list) gv =
  do (gs,_) <- readIORef gv
     let g = snd (get gid gs)
     -- try to add the first node
     writeIORef gv (gs,d)
     nd@(Result de error) <- addnode gid tp name gv
     case error of
       Nothing -> do -- try to add the rest
                     shownodes gid list gv
       Just _ -> return nd


-- adds edges that had been hidden
showedges :: Descr -> [(Int,(Int,Int,String,String))] -> GraphInfo -> IO Result
showedges gid [] gv = do (gs,ev_cnt) <- readIORef gv
                         return (Result ev_cnt Nothing)
showedges gid ((edge@(d,(src,tgt,tp,davinciarc))):list) gv =
  do (gs,_) <- readIORef gv
     let g = snd (get gid gs)
     -- try to add the first edge
     writeIORef gv (gs,d)
     ed@(Result de err) <- addlink gid tp davinciarc src tgt gv
     case err of
       Nothing -> do -- try to add the rest
                     showedges gid list gv
       Just _ -> return ed


-- creates a list of the nodes that will be hidden (ie descriptor,type and name)
saveOldNodes :: AbstractionGraph -> [(Int,(String,DaVinciNode(String,Int,Int)))] -> IO [(Int,(String,String))]
saveOldNodes g [] = return []
saveOldNodes g ((node@(de,(tp,davincinode))):list) = do (name,descr,gid) <- getNodeValue (theGraph g) davincinode
                                                        restOfList <- saveOldNodes g list
                                                        return ((de,(tp,name)):restOfList)


-- creates a list of the edges that will be hidden (ie descriptor,source,target,type and name)
saveOldEdges :: AbstractionGraph -> [(Int,(Int,Int,String,DaVinciArc(String,Int)))] -> IO [(Int,(Int,Int,String,String))]
saveOldEdges g [] = return []
saveOldEdges g (edge@(de,(src,tgt,tp,davinciarc)):list) = do value <- getArcValue (theGraph g) davinciarc
                                                             restOfList <- saveOldEdges g list
                                                             return ((de,(src,tgt,tp,(fst value))):restOfList)





















































