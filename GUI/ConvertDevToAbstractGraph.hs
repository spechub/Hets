module ConvertDevToAbstractGraph where

import DevGraph
import AbstractGraphView
import DaVinciGraph
import GraphDisp
import GraphConfigure
import FiniteMap
import AS_Library
import Graph
--import Main

data ConversionMaps = ConversionMaps {
		        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
		        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv
                      }

type DGraphToAGraphNode = FiniteMap (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = FiniteMap (LIB_NAME,Edge) Descr
type AGraphToDGraphNode = FiniteMap Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = FiniteMap Descr (LIB_NAME,Edge)

convertGraph :: LIB_NAME -> LibEnv -> IO (Descr, GraphInfo)

convertGraph libname libEnv =
  do let convMaps = ConversionMaps
           {dg2abstrNode = emptyFM::DGraphToAGraphNode, 
            abstr2dgNode = emptyFM::AGraphToDGraphNode,
            dg2abstrEdge = emptyFM::DGraphToAGraphEdge,
            abstr2dgEdge = emptyFM::AGraphToDGraphEdge,
            libname2dg = libEnv}
     case lookupFM libEnv libname of
       Just dgraph -> if (isEmpty dgraph) then initializeGraph convMaps
                       else do (abstractGraph,graphInfo) <- initializeGraph convMaps
                               newConvMaps <- convertNodes convMaps abstractGraph graphInfo dgraph libname
                               return (abstractGraph, graphInfo)
		              -- finalConvMaps <- convertEdges newConvMaps dgraph abstractGraph
       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ "does not exist")


initializeGraph :: ConversionMaps -> IO (Descr,GraphInfo)
initializeGraph convMaps =
  do graphInfo <- initgraphs
     Result descr _ <- makegraph "" []
                         [("dg_node",
                           Ellipse $$$ Color "Black" $$$ ValueTitle (\ (s,_,_) -> return s) 
                             {- $$$ LocalMenu 
                              (Button "Show signature" 
                                (\ (name,descr,gid) -> do getSignatureOfNode descr (abstr2dgNode convMaps)
                                ))-}
                               $$$ emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)),
                          ("dg_ref",
                            Box $$$ Color "Blue" $$$ ValueTitle (\ (s,_,_) -> return s)
                              $$$ emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)) ]
                           [] [] graphInfo
     return (descr,graphInfo)


getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO String
getSignatureOfNode descr abstr2dgNode dgraph = 
  case lookupFM abstr2dgNode descr of
    Just (libname, node) -> do let dgnode = lab' (context node dgraph)
                               return (show (dgn_sign dgnode))
    Nothing -> error ("node with descriptor "
                       ++ (show descr) 
                        ++ " has no corresponding node in the development graph")

{-
 LocalMenu ( Button "Unhide abstracted nodes" (
		 \ (name, descr, gid) -> do oldGv <- readIORef gv
					    (Result descr error) <- showIt gid descr gv
					    case error of
						Just _ -> do writeIORef gv oldGv
								                  return ()
								     Nothing -> do redisplay gid gv
								                   return () 
				         )
				      ) $$$ 
-}

convertNodes :: ConversionMaps -> Descr -> GraphInfo -> DGraph -> LIB_NAME -> IO ConversionMaps
{-convertNodes nodeMaps descr graphInfo [] = do return nodeMaps
convertNodes nodeMaps descr graphInfo (node:nodes) = 
  do newNodeMaps <- convertSingleNode nodemaps descr graphInfo node
     return convertNodes newNodeMaps descr graphInfo nodes-}
convertNodes convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertNodesAux convMaps descr graphInfo (labNodes dgraph) libname


convertNodesAux :: ConversionMaps -> Descr -> GraphInfo -> [LNode DGNode] -> LIB_NAME -> IO ConversionMaps
convertNodesAux convMaps descr graphInfo [] libname = return convMaps
convertNodesAux convMaps descr graphInfo ((node,dgnode):lNodes) libname = 
  do Result newDescr _ <- addnode descr (getDGNodeName dgnode) (getDGNodeType dgnode) graphInfo
     newConvMaps <- (convertNodesAux
                       convMaps {dg2abstrNode = addToFM (dg2abstrNode convMaps) (libname, node) descr,
                                 abstr2dgNode = addToFM (abstr2dgNode convMaps) descr (libname, node)}
                                       newDescr graphInfo lNodes libname)
     return newConvMaps
						  
getDGNodeName :: DGNode -> String
getDGNodeName dgnode =
  case get_dgn_name dgnode of
    Just simpleId -> show simpleId
    Nothing -> ""

getDGNodeType :: DGNode -> String
getDGNodeType dgnode =
  case isDGRef dgnode of
    True -> "dg_ref"
    False -> "dg_node"
    

{-(name,
   get_node_shape (map toLower shape) $$$
   Color color $$$
   ValueTitle (\(s,_,_) -> return s) $$$
   LocalMenu (make_menu (local_action_node gid) menu) $$$
   emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int))



 (name,
    get_edge_shape (map toLower shape) $$$
    Color color $$$
    LocalMenu (make_menu (local_action_edge gid) menu) $$$
    emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))


Box
Circle
Ellipse
Rhombus
Triangle
Icon ""

-}
















