module GUI.ConvertDevToAbstractGraph where

import Static.DevGraph
import GUI.AbstractGraphView
import DaVinciGraph
import GraphDisp
import GraphConfigure
import qualified Common.Lib.Map as Map hiding (isEmpty)
import Syntax.AS_Library
import Common.Lib.Graph
import Common.PrettyPrint
import Common.GlobalAnnotationsFunctions
import Data.IORef
import Syntax.Print_HetCASL
import Static.DGToSpec

pretty x = show $ printText0 emptyGlobalAnnos x


{- Maps used to track which node resp edge of the abstract graph correspondes with which of the development graph and vice versa
and one Map to store which libname belongs to which development graph-}

data ConversionMaps = ConversionMaps {
		        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
		        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv }

-- types of the Maps above
type DGraphToAGraphNode = Map.Map (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = Map.Map (LIB_NAME,Edge) Descr
type AGraphToDGraphNode = Map.Map Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = Map.Map Descr (LIB_NAME,Edge)

{- converts the development graph given by its libname into an abstract graph
and returns the descriptor of the latter, the graphInfo it is contained in
and the conversion maps (see above)-}
convertGraph :: LIB_NAME -> LibEnv -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph libname libEnv =
  do let convMaps = ConversionMaps
           {dg2abstrNode = Map.empty::DGraphToAGraphNode, 
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,
            libname2dg = libEnv}
     case Map.lookup libname libEnv of
       Just (_,dgraph,_) -> if (isEmpty dgraph) then 
                                  do (abstractGraph,graphInfo,convRef) <- initializeGraph libname dgraph convMaps
                                     return (abstractGraph, graphInfo,convMaps)
                             else do (abstractGraph,graphInfo,convRef) <- initializeGraph libname dgraph convMaps
                                     newConvMaps <- convertNodes convMaps abstractGraph graphInfo dgraph libname
		                     finalConvMaps <- convertEdges newConvMaps abstractGraph graphInfo dgraph libname
                                     writeIORef convRef finalConvMaps
                                     return (abstractGraph, graphInfo, finalConvMaps)

       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ "does not exist")


{- initializes an empty abstract graph with the needed node and edge types,
return type equals the one of convertGraph -}
initializeGraph :: LIB_NAME -> DGraph -> ConversionMaps
                     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ln dGraph convMaps = do 
  graphInfo <- initgraphs
  event <- newIORef 0
  convRef <- newIORef convMaps
  graphId <- newIORef 0
  Result descr _ <- 
    makegraph ("Development graph for "++show ln) 
               [GlobalMenu(Menu (Just "internal nodes")
                 [Button "Hide" 
                          (do gid <- readIORef graphId
                              Result descr _ <- hidenodetype gid
			                            "internal"
			                            graphInfo
                              writeIORef event descr
                              redisplay gid graphInfo
                              return ()    ),
                  Button "Show" 
                          (do gid <- readIORef graphId
			      descr <- readIORef event
                              showIt gid descr graphInfo
                              redisplay gid graphInfo
                              return ()    )])]
               [("spec",
                 Ellipse $$$ Color "Magenta"
		 $$$ ValueTitle (\ (s,_,_) -> return s) 
                 $$$ LocalMenu 
                    (Button "Show spec" 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           showSpec descr
		                    (abstr2dgNode convMaps)
		                    dGraph
		           return ()
                      ))
                 $$$ emptyNodeTypeParms 
                     :: DaVinciNodeTypeParms (String,Int,Int)),
                ("internal",
                 Ellipse $$$ Color "Grey"
		 $$$ ValueTitle (\ (s,_,_) -> return "")
                 $$$ LocalMenu 
                    (Button "Show spec" 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           showSpec descr (abstr2dgNode convMaps) dGraph
                           return ()
                      ))
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)), 
                ("dg_ref",
                 Box $$$ Color "SteelBlue"
		 $$$ ValueTitle (\ (s,_,_) -> return s)
		 $$$ LocalMenu
		     (Button "Show referenced library"
		     (\ (name,descr,gid) ->
		        do convMaps <- readIORef convRef
                           g <- readIORef graphId
		           newConvMaps <- showReferencedLibrary descr
		                              g
		                              graphInfo
		                              convMaps
		           writeIORef convRef newConvMaps
		           return ()
		     ))
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)) ]
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
                 graphInfo
  writeIORef graphId descr
  return (descr,graphInfo,convRef)

showSpec descr convMap dgraph =
  case Map.lookup descr convMap of
   Nothing -> return ()
   Just (libname,node) -> do
      let sp = dgToSpec dgraph node
      putStrLn (show (printText0_eGA sp))

{- returns the signature of a node as a(n IO) string
used by the node menu defined in initializeGraph-}
getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO String
getSignatureOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> do let dgnode = lab' (context node dgraph)
                               return (show (dgn_sign dgnode))
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
  do Result newDescr err <- addnode descr
			        (getDGNodeType dgnode)
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
    Just simpleId -> pretty simpleId
    Nothing -> ""

-- gets the type of a development graph edge as a string
getDGNodeType :: DGNode -> String
getDGNodeType dgnode =
  case isDGRef dgnode of
    True -> "dg_ref"
    False -> case get_dgn_name dgnode of
               Just _ -> "spec"
               Nothing -> "internal"
    
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


{- den aktuellen AbstractGraph um den neuen DevGraph erweitern:
   - aktuellen AGraph haben wir als Uebergabeparameter
   - neuen DevGraph holen:
     - alten DevGraph holen
     - daraus den DGRef holen
     - daraus den Libname des referenzierten DevGraphen holen
     - damit den neuen DevGraph holen
   - neuen DevGraph an AGraph anhaengen:
     - DevGraph-Knoten umwandeln und in AGraph (und ConversionMaps) adden
     - DevGraph-Kanten umwandeln und in AGraph (und ConversionMaps) adden
     - Verbindungskante zwischen DGRef und referenziertem Knoten einfuegen
       - referenzierten Knoten aus DGRef holen
       - Descr des ref. Knoten aus ConversionMaps holen
       - Kante in AGraph adden
-}
showReferencedLibrary :: Descr -> Descr -> GraphInfo -> ConversionMaps -> IO ConversionMaps
showReferencedLibrary descr abstractGraph graphInfo convMaps =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,node) -> 
         case Map.lookup libname libname2dgMap of
	  Just (_,dgraph,_) -> 
            do let (_,(DGRef _ refLibname refNode)) = labNode' (context node dgraph)
	       case Map.lookup refLibname libname2dgMap of
                 Just (_,refDgraph,_) -> 
		   if (isEmpty refDgraph) then do return convMaps
                    else do convMaps' <- convertNodesAux convMaps
		                             abstractGraph
				             graphInfo
				             (labNodes refDgraph)
				             libname
                            newConvMaps' <- convertEdgesAux convMaps'
				                abstractGraph
					        graphInfo
					        (labEdges refDgraph)
					        libname
                            case Map.lookup (libname,refNode) (dg2abstrNode newConvMaps') of
                              Just refDescr -> do addlink descr "reference" "" descr refDescr graphInfo
				  	          return (newConvMaps' {dg2abstrEdge =
						           Map.insert (libname, (node,refNode))
							       refDescr
				                               (dg2abstrEdge convMaps),
							   abstr2dgEdge = Map.insert refDescr
				                               (libname, (node,refNode))
				                               (abstr2dgEdge convMaps)})
			      Nothing -> error "adding referenced node failed"
                 Nothing -> error ("The referenced library ("
				     ++ (show refLibname)
				     ++ ") is unknown")

	       
          Nothing ->
	    error ("Unknown library: " ++ (show libname))
    Nothing ->
      error ("there is no node with the descriptor "
	         ++ show descr)

    where libname2dgMap = libname2dg convMaps













