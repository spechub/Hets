-- needs ghc

{- GUI/ConvertDevToAbstractGraph.hs
   $Id$
   Jorina Freya Gerken, Till Mossakowski

   Conversion of development graphs from Logic.DevGraph
   to abstract graphs of the graph display interface

   todo:
   hiding of internal nodes:
    internal nodes that are not between named nodes should be kept
   display inclusions and inter-logic links in special colour
   try different graph layout algorithms for daVinci (dot?)
   close program when all windows are closed
-}

module GUI.ConvertDevToAbstractGraph where

import Static.DevGraph
import GUI.AbstractGraphView
import DaVinciGraph
import GraphDisp
import GraphConfigure

import qualified Common.Lib.Map as Map hiding (isEmpty)
import Syntax.AS_Library
import Syntax.Print_HetCASL

import Common.Lib.Graph
import Common.Id
import Data.IORef
import Static.DGToSpec
import List(nub)

import Logic.Grothendieck
import Logic.Logic



{- Maps used to track which node resp edge of the abstract graph correspondes with which of the development graph and vice versa
and one Map to store which libname belongs to which development graph-}

data ConversionMaps = ConversionMaps {
		        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
		        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv}

data GraphMem = GraphMem {
		  graphInfo :: GraphInfo,
		  nextGraphId :: Descr}

-- types of the Maps above
type DGraphToAGraphNode = Map.Map (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = Map.Map (LIB_NAME,Edge) Descr
type AGraphToDGraphNode = Map.Map Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = Map.Map Descr (LIB_NAME,Edge)

initializeConverter :: IO (IORef GraphMem)
initializeConverter = do initGraphInfo <- initgraphs
		         graphMem <- (newIORef GraphMem{nextGraphId = 0, graphInfo = initGraphInfo})
			 return graphMem

{- converts the development graph given by its libname into an abstract graph
and returns the descriptor of the latter, the graphInfo it is contained in
and the conversion maps (see above)-}
convertGraph :: IORef GraphMem -> LIB_NAME -> LibEnv -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph graphMem libname libEnv =
  do --nextGraphId <- newIORef 0
     let convMaps = ConversionMaps
           {dg2abstrNode = Map.empty::DGraphToAGraphNode, 
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,
            libname2dg = libEnv}

     case Map.lookup libname libEnv of
       Just (_,_,dgraph) -> if (isEmpty dgraph) then 
                                  do (abstractGraph,graphInfo,convRef) <- initializeGraph graphMem libname
									  dgraph convMaps
                                     return (abstractGraph, graphInfo,convMaps)
                             else do (abstractGraph,graphInfo,convRef) <- initializeGraph graphMem libname
									  dgraph convMaps
                                     newConvMaps <- convertNodes convMaps abstractGraph graphInfo dgraph libname
		                     finalConvMaps <- convertEdges newConvMaps abstractGraph graphInfo dgraph libname
                                     writeIORef convRef finalConvMaps
                                     return (abstractGraph, graphInfo, finalConvMaps)

       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ "does not exist")


{- initializes an empty abstract graph with the needed node and edge types,
return type equals the one of convertGraph -}
initializeGraph :: IORef GraphMem ->LIB_NAME -> DGraph -> ConversionMaps
                     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ioRefGraphMem ln dGraph convMaps = do 
  graphMem <- readIORef ioRefGraphMem
  event <- newIORef 0
  convRef <- newIORef convMaps
  ioRefSubtreeEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  ioRefVisibleNodes <- newIORef [(Common.Lib.Graph.nodes dGraph)]
  let gid = nextGraphId graphMem -- newIORef (nextGraphId convMaps)
      actGraphInfo = graphInfo graphMem
--  graphId <- newIORef 0
  Result descr _ <- 
    makegraph ("Development graph for "++show ln) 
               [GlobalMenu(Menu (Just "internal nodes")
                 [Button "Hide" 
                          (do --gid <- readIORef graphId
                              Result descr _ <- hidenodetype gid
			                            "internal"
			                            actGraphInfo
                              writeIORef event descr
                              redisplay gid actGraphInfo
                              return ()    ),
                  Button "Show" 
                          (do --gid <- readIORef graphId
			      descr <- readIORef event
                              showIt gid descr actGraphInfo
                              redisplay gid actGraphInfo
                              return ()    )])]
               [("spec", 
		 createLocalMenuNodeTypeSpec "Magenta" convRef dGraph
                              ioRefSubtreeEvents ioRefVisibleNodes
                                  actGraphInfo ioRefGraphMem
                ),
                ("locallyEmpty_spec", 
		 createLocalMenuNodeTypeSpec "Violet" convRef dGraph
                                          ioRefSubtreeEvents ioRefVisibleNodes
                                              actGraphInfo ioRefGraphMem),
                ("internal", 
		 createLocalMenuNodeTypeInternal "Grey" convRef dGraph
                ),
		("locallyEmpty_internal", 
		 createLocalMenuNodeTypeInternal "LightGrey" convRef dGraph),
                ("dg_ref", 
		 createLocalMenuNodeTypeDgRef "SteelBlue" convRef actGraphInfo ioRefGraphMem graphMem
                 ),
		("locallyEmpty_dg_ref", 
		 createLocalMenuNodeTypeDgRef "LightSteelBlue" convRef actGraphInfo ioRefGraphMem graphMem
                 ) ]
                 [("globaldef",
                   Solid 
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
		  ("def",
                   Solid $$$ Color "Steelblue"
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
                  ("proventhm",
                   Solid $$$ Color "Green" 
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
                  ("unproventhm",
                   Solid $$$ Color "Red" 
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
                  -- > ######### welche Farbe fuer reference ##########
                  ("reference",
                   Dotted $$$ Color "Grey"
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))]
                 [("globaldef","globaldef","globaldef"),
		  ("globaldef","def","def"),
                  ("globaldef","proventhm","proventhm"),
                  ("globaldef","unproventhm","unproventhm"),
		  ("def","globaldef","def"),
		  ("def","def","def"),
                  ("def","proventhm","proventhm"),
                  ("def","unproventhm","unproventhm"),
                  ("proventhm","globaldef","proventhm"),
                  ("proventhm","def","proventhm"),
                  ("proventhm","proventhm","proventhm"),
                  ("proventhm","unproventhm","unproventhm"),
                  ("unproventhm","globaldef","unproventhm"),
                  ("unproventhm","def","unproventhm"),
                  ("unproventhm","proventhm","unproventhm"),
                  ("unproventhm","unproventhm","unproventhm")] 
                 actGraphInfo
  writeIORef ioRefGraphMem graphMem{nextGraphId = gid+1}
  graphMem'<- readIORef ioRefGraphMem
  return (descr,graphInfo graphMem',convRef)

-- *************************************************************
-- methods to create the local menus of the different nodetypes
-- *************************************************************

-- local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec color convRef dGraph ioRefSubtreeEvents ioRefVisibleNodes actGraphInfo ioRefGraphMem =
                 Ellipse $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return s) 
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSpec convRef dGraph,
		    createLocalMenuButtonShowSignature convRef dGraph,
		    createLocalMenuButtonShowSublogic convRef dGraph,
		    createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents convRef
		                                         ioRefVisibleNodes ioRefGraphMem
		                                         actGraphInfo,
		    createLocalMenuButtonUndoShowJustSubtree ioRefVisibleNodes 
		                                             ioRefSubtreeEvents                                                                                                        actGraphInfo
		   ])
                  $$$ emptyNodeTypeParms 
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal color convRef dGraph =
                 Ellipse $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return "")
                 $$$ LocalMenu (Menu (Just "node menu")
                    [createLocalMenuButtonShowSpec convRef dGraph,
		     createLocalMenuButtonShowSignature convRef dGraph,
 		     createLocalMenuButtonShowSublogic convRef dGraph])
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef color convRef actGraphInfo ioRefGraphMem graphMem = 
                 Box $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return s)
		 $$$ LocalMenu (Button "Show referenced library"
		     (\ (name,descr,gid) ->
		        do convMaps <- readIORef convRef
                           --g <- readIORef graphId
		           (refDescr, newGraphInfo, refConvMaps) <- showReferencedLibrary ioRefGraphMem descr
		                              gid
		                              actGraphInfo
		                              convMaps
		           
--writeIORef convRef newConvMaps
                           writeIORef ioRefGraphMem graphMem{graphInfo = newGraphInfo, nextGraphId = refDescr +1}
                           redisplay refDescr newGraphInfo
		          -- redisplay gid graphInfo
		           return ()
		     ))
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)


-- menu button for local menus to show the spec of a node
createLocalMenuButtonShowSpec convRef dGraph =
                    (Button "Show spec" 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           showSpec descr
		                    (abstr2dgNode convMaps)
		                    dGraph
		           return ()
                       )
	            )


-- menu button for local menus to show the spec of a node
createLocalMenuButtonShowSignature convRef dgraph =
                    (Button "Show signature" 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           getSignatureOfNode descr
		                              (abstr2dgNode convMaps)
		                              dgraph
		           return ()
                       )
	            )


createLocalMenuButtonShowSublogic convRef dgraph =
                    (Button "Show sublogic" 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           getSublogicOfNode descr
		                             (abstr2dgNode convMaps)
		                             dgraph
		           return ()
                       )
	            )


createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents convRef ioRefVisibleNodes ioRefGraphMem actGraphInfo = 
                    (Button "Show just subtree"
		      (\ (name,descr,gid) ->
		        do subtreeEvents <- readIORef ioRefSubtreeEvents
		           case Map.lookup descr subtreeEvents of
                             Just _ -> putStrLn ("it is already just the subtree of node " ++ (show descr) ++" shown")
		             Nothing -> 
                               do convMaps <- readIORef convRef
                                  visibleNodes <- readIORef ioRefVisibleNodes
			          (eventDescr,newVisibleNodes,errorMsg) <- showJustSubtree ioRefGraphMem
				 	    				    descr gid convMaps visibleNodes
		                  case errorMsg of
		                    Nothing -> do let newSubtreeEvents = Map.insert descr eventDescr subtreeEvents
                                                  writeIORef ioRefSubtreeEvents newSubtreeEvents
					          writeIORef ioRefVisibleNodes newVisibleNodes
		                                  redisplay gid actGraphInfo
		                                  return()
		                    Just text -> do putStrLn text
		                                    return()                            
		      )
                    )


createLocalMenuButtonUndoShowJustSubtree ioRefVisibleNodes ioRefSubtreeEvents actGraphInfo =
                    (Button "undo show just subtree"
		      (\ (name,descr,gid) ->
		        do visibleNodes <- readIORef ioRefVisibleNodes
                           case (tail visibleNodes) of
                             [] -> do putStrLn "Complete graph is already shown"
                                      return()
                             newVisibleNodes@(x:xs) ->
                               do subtreeEvents <- readIORef ioRefSubtreeEvents
                                  case Map.lookup descr subtreeEvents of
                                    Just hide_event -> 
		                      do showIt gid hide_event actGraphInfo
                                         writeIORef ioRefSubtreeEvents (Map.delete descr subtreeEvents)
                                         writeIORef ioRefVisibleNodes newVisibleNodes
		                         redisplay gid actGraphInfo
		                         return ()
		                    Nothing -> do putStrLn "undo not possible"
		                                  return()
                      )
		    )
-- ******************************
-- end of local menu definitions
-- ******************************


showSpec descr convMap dgraph =
  case Map.lookup descr convMap of
   Nothing -> return ()
   Just (libname,node) -> do
      let sp = dgToSpec dgraph node
      putStrLn (show (printText0_eGA sp))


{- outputs the signature of a node in the bash;
used by the node menu defined in initializeGraph-}
getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSignatureOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      do let dgnode = lab' (context node dgraph)
	 case dgnode of
           (DGNode _ _ _ _) -> putStrLn (show (dgn_sign dgnode))
           (DGRef _ _ _) -> error ( "nodes of type dg_ref do not have a signature")
           otherwise -> error ( "unknown type of node")
    Nothing -> error ("node with descriptor "
                       ++ (show descr) 
                        ++ " has no corresponding node in the development graph")


{- outputs the sublogic of a node in the bash;
used by the node menu defined in initializeGraph-}
getSublogicOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSublogicOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      do let dgnode = lab' (context node dgraph)
	 case dgnode of
           (DGNode _ _ _ _) ->
	     case (dgn_sign dgnode) of
	       G_sign lid sigma ->
		 do putStrLn (head (sublogic_names lid (min_sublogic_sign lid sigma)))
               otherwise -> error ("no sublogic found")
           (DGRef _ _ _) -> error ( "nodes of type dg_ref do not have a sublogic")
           otherwise -> error ( "unknown type of node")
    Nothing -> error ("node with descriptor "
                       ++ (show descr) 
                        ++ " has no corresponding node in the development graph")


{- converts the nodes of the development graph, if it has any,
and returns the resulting conversion maps
if the graph is empty the conversion maps are returned unchanged-}
convertNodes :: ConversionMaps -> Descr -> GraphInfo -> DGraph
                  -> LIB_NAME -> IO ConversionMaps
convertNodes convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertNodesAux convMaps
		                descr
				graphInfo
				(labNodes dgraph)
				libname


{- auxiliar function for convertNodes
if the given list of nodes is emtpy, it returns the conversion maps unchanged
otherwise it adds the converted first node to the abstract graph and to the affected conversion maps
and afterwards calls itself with the remaining node list -}
convertNodesAux :: ConversionMaps -> Descr -> GraphInfo ->
		     [LNode DGNode] -> LIB_NAME -> IO ConversionMaps
convertNodesAux convMaps descr graphInfo [] libname = return convMaps
convertNodesAux convMaps descr graphInfo ((node,dgnode):lNodes) libname = 
  do nodetype <- (getDGNodeType dgnode)
     Result newDescr err <- addnode descr
			        nodetype
				(getDGNodeName dgnode)
				graphInfo
     --putStrLn (maybe "" id err)
     newConvMaps <- (convertNodesAux
                       convMaps {dg2abstrNode = Map.insert (libname, node) newDescr (dg2abstrNode convMaps),
                                 abstr2dgNode = Map.insert newDescr (libname, node) (abstr2dgNode convMaps)}
                                       descr graphInfo lNodes libname)
     return newConvMaps

-- gets the name of a development graph node as a string						  
getDGNodeName :: DGNode -> String
getDGNodeName dgnode =
  case get_dgn_name dgnode of
    Just simpleId -> tokStr simpleId
    Nothing -> ""

-- gets the type of a development graph edge as a string
getDGNodeType :: DGNode -> IO String
getDGNodeType dgnode =
  do let nodetype = getDGNodeTypeAux dgnode
     case (isDGRef dgnode) of
       True -> return (nodetype++"dg_ref")
       False -> case get_dgn_name dgnode of
                  Just _ -> return (nodetype++"spec")
                  Nothing -> return (nodetype++"internal")
    
getDGNodeTypeAux :: DGNode -> String
getDGNodeTypeAux dgnode = if (locallyEmpty dgnode) then "locallyEmpty_"
                           else ""

getDGLinkType :: DGLinkType -> String
getDGLinkType LocalDef = "def"
getDGLinkType GlobalDef = "globaldef"
getDGLinkType HidingDef = "def"
getDGLinkType (FreeDef _) = "def"
getDGLinkType (CofreeDef _) = "def"
getDGLinkType (LocalThm bool) = getThmType bool
getDGLinkType (GlobalThm bool) = getThmType bool
getDGLinkType (HidingThm _ bool) = getThmType bool
getDGLinkType (FreeThm _ bool) = getThmType bool

getThmType :: Bool -> String
getThmType bool =
  case bool of
    True -> "proventhm"
    False -> "unproventhm"

{- converts the edges of the development graph
works the same way as convertNods does-}
convertEdges :: ConversionMaps -> Descr -> GraphInfo -> DGraph
	          -> LIB_NAME -> IO ConversionMaps
convertEdges convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertEdgesAux convMaps
		                descr
				graphInfo
				(labEdges dgraph)
				libname

-- function context from Graph.hs with inverse arguments
invContext :: DGraph -> Node -> Context DGNode DGLink
invContext dgraph node = context node dgraph

{- auxiliar function for convertEges --> not yet implemented! -}
convertEdgesAux :: ConversionMaps -> Descr -> GraphInfo -> 
                    [LEdge DGLink] -> LIB_NAME -> IO ConversionMaps
convertEdgesAux convMaps descr graphInfo [] libname = return convMaps
convertEdgesAux convMaps descr graphInfo ((src,tar,edge):lEdges) libname = 
  do let srcnode = Map.lookup (libname,src) (dg2abstrNode convMaps)
         tarnode = Map.lookup (libname,tar) (dg2abstrNode convMaps)
     case (srcnode,tarnode) of 
      (Just s, Just t) -> do
        Result newDescr err <- addlink descr (getDGLinkType (dgl_type edge))
                                   "" s t graphInfo
        --putStrLn (maybe "" id err)
        --putStrLn ("Adding link" ++ show descr)
        newConvMaps <- (convertEdgesAux
                       convMaps {dg2abstrEdge = Map.insert (libname, (src,tar))
				                     newDescr
				                     (dg2abstrEdge convMaps),
                                 abstr2dgEdge = Map.insert newDescr
				                     (libname, (src,tar))
				                     (abstr2dgEdge convMaps)}
                                       descr graphInfo lEdges libname)
        return newConvMaps
      otherwise -> error "Cannot find nodes"


showReferencedLibrary :: IORef GraphMem -> Descr -> Descr -> GraphInfo -> ConversionMaps -> IO (Descr, GraphInfo, ConversionMaps)
showReferencedLibrary graphMem descr abstractGraph graphInfo convMaps =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,node) -> 
         case Map.lookup libname libname2dgMap of
	  Just (_,_,dgraph) -> 
            do let (_,(DGRef _ refLibname refNode)) = labNode' (context node dgraph)
	       case Map.lookup refLibname libname2dgMap of
                 Just (_,refDgraph,_) -> convertGraph graphMem refLibname (libname2dg convMaps)
		 Nothing -> error ("The referenced library ("
				     ++ (show refLibname)
				     ++ ") is unknown")
          Nothing ->
	    error ("Selected node belongs to unknown library: " ++ (show libname))
    Nothing ->
      error ("there is no node with the descriptor "
	         ++ show descr)

    where libname2dgMap = libname2dg convMaps

-- ###################################################################
-- returntype festlegen
showJustSubtree:: IORef GraphMem -> Descr -> Descr -> ConversionMaps -> [[Node]]-> IO (Descr, [[Node]], Maybe String)
showJustSubtree ioRefGraphMem descr abstractGraph convMaps visibleNodes =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,parentNode) ->
      case Map.lookup libname libname2dgMap of
	Just (_,_,dgraph) -> 
	  do let -- allDgNodes = Common.Lib.Graph.nodes dgraph
                 allNodes = getNodeDescriptors (head visibleNodes) libname convMaps -- allDgNodes libname convMaps
                 dgNodesOfSubtree = nub (parentNode:(getNodesOfSubtree dgraph visibleNodes parentNode))
                 -- the selected node (parentNode) shall not be hidden either,
                 -- and we already know its descriptor (descr)
		 nodesOfSubtree = getNodeDescriptors dgNodesOfSubtree libname convMaps
	         nodesToHide = filter (notElemR nodesOfSubtree) allNodes
	     graphMem <- readIORef ioRefGraphMem
	     (Result eventDescr errorMsg) <- hidenodes abstractGraph nodesToHide (graphInfo graphMem)
	     return (eventDescr, (dgNodesOfSubtree:visibleNodes), errorMsg)
{-	     case errorMsg of 
	       Just text -> return (-1,text)
	       Nothing -> return (eventDescr,
			  return convMaps-}
        Nothing ->
	    error ("showJustSubtree: Selected node belongs to unknown library: " ++ (show libname))
    Nothing ->
      error ("showJustSubtree: there is no node with the descriptor "
	         ++ show descr)

    where libname2dgMap = libname2dg convMaps



getNodeDescriptors :: [Node] -> LIB_NAME -> ConversionMaps -> [Descr]
getNodeDescriptors [] _ _ = []
getNodeDescriptors (node:nodelist) libname convMaps =
  case Map.lookup (libname,node) (dg2abstrNode convMaps) of
    Just descr -> descr:(getNodeDescriptors nodelist libname convMaps)
    Nothing -> error ("getNodeDescriptors: There is no descriptor for dgnode " ++ (show node))


getNodesOfSubtree :: DGraph -> [[Node]] -> Node -> [Node]
getNodesOfSubtree dgraph visibleNodes node = (concat (map (getNodesOfSubtree dgraph visibleNodes) predOfNode))++predOfNode

    where predOfNode = filter (elemR (head visibleNodes)) (pre dgraph node)

elemR :: Eq a => [a] -> a -> Bool
elemR list element = elem element list

notElemR :: Eq a => [a] -> a -> Bool
notElemR list element = notElem element list
