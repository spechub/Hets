module ConvertDevToAbstractGraph where

import DevGraph
import AbstractGraphView
import DaVinciGraph
import GraphDisp
import GraphConfigure
import FiniteMap
import AS_Library
import Graph

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
       Just (_,dgraph,_) -> if (isEmpty dgraph) then initializeGraph convMaps
                             else do (abstractGraph,graphInfo,_) <- initializeGraph convMaps
                                     newConvMaps <- convertNodes convMaps abstractGraph graphInfo dgraph libname
		                     finalConvMaps <- convertEdges newConvMaps abstractGraph graphInfo dgraph libname
                                     return (abstractGraph, graphInfo, finalConvMaps)

       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ "does not exist")

{- initializes an empty abstract graph with the needed node and edge types,
return type equals the one of convertGraph -}
initializeGraph :: ConversionMaps -> IO (Descr,GraphInfo,ConversionMaps)
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
     return (descr,graphInfo,convMaps)


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
  do Result newDescr _ <- addnode descr (getDGNodeType dgnode) (getDGNodeName dgnode) graphInfo
     newConvMaps <- (convertNodesAux
                       convMaps {dg2abstrNode = addToFM (dg2abstrNode convMaps) (libname, node) descr,
                                 abstr2dgNode = addToFM (abstr2dgNode convMaps) descr (libname, node)}
                                       newDescr graphInfo lNodes libname)
     return newConvMaps

-- gets the name of a development graph node as a string						  
getDGNodeName :: DGNode -> String
getDGNodeName dgnode =
  case get_dgn_name dgnode of
    Just simpleId -> show simpleId
    Nothing -> ""

-- gets the type of a development graph edge as a string
getDGNodeType :: DGNode -> String
getDGNodeType dgnode =
  case isDGRef dgnode of
    True -> "dg_ref"
    False -> "dg_node"
    

{- converts the edges of the development graph
works the same way as convertNodes does-}
convertEdges :: ConversionMaps -> Descr -> GraphInfo -> DGraph -> LIB_NAME -> IO ConversionMaps
convertEdges convMaps descr graphInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertEdgesAux convMaps descr graphInfo (map (invContext dgraph) (Graph.nodes dgraph)) libname

-- function context from Graph.hs with inverse arguments
invContext :: DGraph -> Node -> Context DGNode DGLink
invContext dgraph node = context node dgraph

{- auxiliar function for convertEges --> not yet implemented! -}
convertEdgesAux :: ConversionMaps -> Descr -> GraphInfo -> [Context DGNode DGLink] -> LIB_NAME -> IO ConversionMaps
convertEdgesAux convMaps descr graphInfo [] libname = do return convMaps
convertEdgesAux convMaps descr graphInfo ((preds,node,_,succs):contexts) libname = error ("not yet implemented")




