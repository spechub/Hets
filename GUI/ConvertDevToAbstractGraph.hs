module ConvertDevToAbstractGraph where

import DevGraph
import AbstractGraphView
import DaVinciGraph
import GraphDisp
import GraphConfigure
import FiniteMap
import AS_Library
import Common.Lib.Graph
import PrettyPrint
import GlobalAnnotationsFunctions
import Data.IORef
import Print_HetCASL
import DGToSpec

pretty x = show $ printText0 emptyGlobalAnnos x


{- FiniteMaps used to track which node resp edge of the abstract graph correspondes with which of the development graph and vice versa
and one FiniteMap to store which libname belongs to which development graph-}
data ConversionMaps = ConversionMaps {
		        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
		        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv
                      }

-- types of the FiniteMaps above
type DGraphToAGraphNode = FiniteMap (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = FiniteMap (LIB_NAME,Edge) Descr
type AGraphToDGraphNode = FiniteMap Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = FiniteMap Descr (LIB_NAME,Edge)

{- converts the development graph given by its libname into an abstract graph
and returns the descriptor of the latter, the graphInfo it is contained in and the conversion maps (see above)-}
convertGraph :: LIB_NAME -> LibEnv -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph libname libEnv =
  do let convMaps = ConversionMaps
           {dg2abstrNode = emptyFM::DGraphToAGraphNode, 
            abstr2dgNode = emptyFM::AGraphToDGraphNode,
            dg2abstrEdge = emptyFM::DGraphToAGraphEdge,
            abstr2dgEdge = emptyFM::AGraphToDGraphEdge,
            libname2dg = libEnv}
     case lookupFM libEnv libname of
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
initializeGraph :: LIB_NAME -> DGraph -> ConversionMaps -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ln dGraph convMaps = do 
  graphInfo <- initgraphs
  event <- newIORef 0
  convRef <- newIORef convMaps
  Result descr _ <- 
    makegraph ("Development graph for "++show ln) 
               [GlobalMenu(Menu (Just "internal nodes")
                 [Button "Hide" 
                          (do Result descr _ <- hidenodetype 0 "internal" graphInfo
                              writeIORef event descr
                              redisplay 0 graphInfo
                              return ()    ),
                  Button "Show" 
                          (do descr <- readIORef event
                              showIt 0 descr graphInfo
                              redisplay 0 graphInfo
                              return ()    )])]
               [("spec",
                 Ellipse $$$ Color "Magenta" $$$ ValueTitle (\ (s,_,_) -> return s) 
                 $$$ LocalMenu 
                    (Button "Show spec" 
                      (\ (name,descr,gid) -> do convMaps <- readIORef convRef
                                                showSpec descr (abstr2dgNode convMaps) dGraph
                                                return ()
                      ))
                     $$$ emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)),
                ("internal",
                 Ellipse $$$ Color "Grey" $$$ ValueTitle (\ (s,_,_) -> return "")
                 $$$ LocalMenu 
                    (Button "Show spec" 
                      (\ (name,descr,gid) -> do convMaps <- readIORef convRef
                                                showSpec descr (abstr2dgNode convMaps) dGraph
                                                return ()
                      ))
                  $$$ emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)), 
                ("dg_ref",
                  Box $$$ Color "SteelBlue" $$$ ValueTitle (\ (s,_,_) -> return s)
                    $$$ emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)) ]
                 [("def",
                    Solid $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
                  ("proventhm",
                    Solid $$$ Color "Green" $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int)),
                  ("unproventhm",
                    Solid $$$ Color "Red" $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))]
                 [("def","def","def"),
                  ("def","proventhm","proventhm"),
                  ("def","unproventhm","unproventhm"),
                  ("proventhm","def","proventhm"),
                  ("proventhm","proventhm","proventhm"),
                  ("proventhm","unproventhm","unproventhm"),
                  ("unproventhm","def","unproventhm"),
                  ("unproventhm","proventhm","unproventhm"),
                  ("unproventhm","unproventhm","unproventhm")] graphInfo
  return (descr,graphInfo,convRef)

showSpec descr convMap dgraph =
  case lookupFM convMap descr of
   Nothing -> return ()
   Just (libname,node) -> do
      let sp = dgToSpec dgraph node
      putStrLn (show (printText0_eGA sp))

{- returns the signature of a node as a(n IO) string
used by the node menu defined in initializeGraph-}
getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO String
getSignatureOfNode descr ab2dgNode dgraph = 
  case lookupFM ab2dgNode descr of
    Just (libname, node) -> do let dgnode = lab' (context node dgraph)
                               return (show (dgn_sign dgnode))
    Nothing -> error ("node with descriptor "
                       ++ (show descr) 
                        ++ " has no corresponding node in the development graph")

{- converts the nodes of the development graph, if it has any,
and returns the resulting conversion maps
if the graph is empty the conversion maps are returned unchanged-}
convertNodes :: ConversionMaps -> Descr -> GraphInfo -> DGraph -> LIB_NAME -> IO ConversionMaps
convertNodes convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertNodesAux convMaps descr graphInfo (labNodes dgraph) libname


{- auxiliar function for convertNodes
if the given list of nodes is emtpy, it returns the conversion maps unchanged
otherwise it adds the converted first node to the abstract graph and to the affected conversion maps
and afterwards calls itself with the remaining node list -}
convertNodesAux :: ConversionMaps -> Descr -> GraphInfo -> [LNode DGNode] -> LIB_NAME -> IO ConversionMaps
convertNodesAux convMaps descr graphInfo [] libname = return convMaps
convertNodesAux convMaps descr graphInfo ((node,dgnode):lNodes) libname = 
  do Result newDescr err <- addnode descr (getDGNodeType dgnode) (getDGNodeName dgnode) graphInfo
     --putStrLn (maybe "" id err)
     newConvMaps <- (convertNodesAux
                       convMaps {dg2abstrNode = addToFM (dg2abstrNode convMaps) (libname, node) newDescr,
                                 abstr2dgNode = addToFM (abstr2dgNode convMaps) newDescr (libname, node)}
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
getDGLinkType GlobalDef = "def"
getDGLinkType HidingDef = "def"
getDGLinkType (FreeDef _) = "def"
getDGLinkType (CofreeDef _) = "def"
getDGLinkType (LocalThm bool) = getThmType bool
getDGLinkType (GlobalThm bool) = getThmType bool
getDGLinkType (HidingThm _ bool) = getThmType bool
getDGLinkType (FreeThm _ bool) = getThmType bool

getThmType :: Bool -> String
getThmType bool = case bool of
  True -> "proventhm"
  False -> "unproventhm"

{- converts the edges of the development graph
works the same way as convertNods does-}
convertEdges :: ConversionMaps -> Descr -> GraphInfo -> DGraph -> LIB_NAME -> IO ConversionMaps
convertEdges convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertEdgesAux convMaps descr graphInfo dgraph (labEdges dgraph) libname

-- function context from Graph.hs with inverse arguments
invContext :: DGraph -> Node -> Context DGNode DGLink
invContext dgraph node = context node dgraph

{- auxiliar function for convertEges --> not yet implemented! -}
convertEdgesAux :: ConversionMaps -> Descr -> GraphInfo -> DGraph ->
                    [LEdge DGLink] -> LIB_NAME -> IO ConversionMaps
convertEdgesAux convMaps descr graphInfo dgraph [] libname = return convMaps
convertEdgesAux convMaps descr graphInfo dgraph ((src,tar,edge):lEdges) libname = 
  do let srcnode = lookupFM (dg2abstrNode convMaps) (libname,src)
         tarnode = lookupFM (dg2abstrNode convMaps) (libname,tar)
     case (srcnode,tarnode) of 
      (Just s, Just t) -> do
        Result newDescr err <- addlink descr (getDGLinkType (dgl_type edge)) "" s t graphInfo
        --putStrLn (maybe "" id err)
        --putStrLn ("Adding link" ++ show descr)
        newConvMaps <- (convertEdgesAux
                       convMaps {dg2abstrEdge = addToFM (dg2abstrEdge convMaps) (libname, (src,tar)) newDescr,
                                 abstr2dgEdge = addToFM (abstr2dgEdge convMaps) newDescr (libname, (src,tar))}
                                       descr graphInfo dgraph lEdges libname)
        return newConvMaps
      otherwise -> error "Cannot find nodes"





