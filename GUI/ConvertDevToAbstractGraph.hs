{-
Module      :  $Header$
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

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

import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Comorphisms.LogicGraph
import Static.DevGraph
import Static.DGToSpec
import Proofs.Proofs

import GUI.AbstractGraphView
import GUI.ShowLogicGraph
import DaVinciGraph
import GraphDisp
import GraphConfigure
import TextDisplay
import Configuration
import qualified HTk
import Core

import qualified Common.Lib.Map as Map hiding (isEmpty)
import Common.Lib.Graph
import Common.Id
import Common.Lib.Pretty as Pretty hiding (isEmpty)
import Common.PrettyPrint
import qualified Common.Result as Res
import Syntax.AS_Library
import Common.AS_Annotation
import Common.GlobalAnnotations

import Options

import Data.IORef
import Data.Maybe
import List(nub)
import Control.Monad

import Debug.Trace

{- Maps used to track which node resp edge of the abstract graph
correspondes with which of the development graph and vice versa and
one Map to store which libname belongs to which development graph-}

data ConversionMaps = ConversionMaps {
		        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
		        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv}
                      deriving Show

instance PrettyPrint String where
    printText0 ga c = ptext (take 25 c)

instance  Common.PrettyPrint.PrettyPrint ConversionMaps where
  printText0 ga convMaps =
       ptext "dg2abstrNode"
    Pretty.$$ (printText0 ga $ dg2abstrNode convMaps)
    Pretty.$$ ptext "dg2abstrEdge"
    Pretty.$$ (printText0 ga $ dg2abstrEdge convMaps)
    Pretty.$$ ptext "abstr2dgNode"
    Pretty.$$ (printText0 ga $ abstr2dgNode convMaps)
    Pretty.$$ ptext "abstr2dgEdge"
    Pretty.$$ (printText0 ga $ abstr2dgEdge convMaps)

data GraphMem = GraphMem {
		  graphInfo :: GraphInfo,
		  nextGraphId :: Descr}

-- types of the Maps above
type DGraphToAGraphNode = Map.Map (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = Map.Map (LIB_NAME,(Descr,Descr,String)) Descr
type AGraphToDGraphNode = Map.Map Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = Map.Map Descr (LIB_NAME,(Descr,Descr,String))

initializeConverter :: IO (IORef GraphMem)
initializeConverter = 
    do HTk.initHTk [HTk.withdrawMainWin]
       showLogicGraph daVinciSort
       initGraphInfo <- initgraphs
       graphMem <- (newIORef GraphMem{nextGraphId = 0, 
				      graphInfo = initGraphInfo})
       return graphMem

{- converts the development graph given by its libname into an abstract graph
and returns the descriptor of the latter, the graphInfo it is contained in
and the conversion maps (see above)-}

convertGraph :: IORef GraphMem -> LIB_NAME -> LibEnv 
	     -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph graphMem libname libEnv =
  do --nextGraphId <- newIORef 0
     let convMaps = ConversionMaps
           {dg2abstrNode = Map.empty::DGraphToAGraphNode, 
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,
            libname2dg = libEnv}

     case Map.lookup libname libEnv of

       Just globContext@(_,_,dgraph) -> 
	 if (isEmpty dgraph) then 
	   do (abstractGraph,graphInfo,convRef) <-
	          initializeGraph graphMem libname dgraph convMaps globContext
              return (abstractGraph, graphInfo,convMaps)
          else 
	    do (abstractGraph,graphInfo,convRef) <-
		   initializeGraph graphMem libname dgraph convMaps globContext
               newConvMaps <- convertNodes convMaps abstractGraph
			      graphInfo dgraph libname
	       finalConvMaps <- convertEdges newConvMaps abstractGraph 
				graphInfo dgraph libname
               writeIORef convRef finalConvMaps
               return (abstractGraph, graphInfo, finalConvMaps)
                     
       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ " does not exist")


{- initializes an empty abstract graph with the needed node and edge types,
return type equals the one of convertGraph -}
initializeGraph :: IORef GraphMem ->LIB_NAME -> DGraph -> ConversionMaps
                     -> GlobalContext 
		     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ioRefGraphMem ln dGraph convMaps globContext = do 
  graphMem <- readIORef ioRefGraphMem
  event <- newIORef 0
  convRef <- newIORef convMaps
  ioRefProofStatus <- newIORef (globContext, libname2dg convMaps,
		                [([]::[DGRule], []::[DGChange])],
				dGraph)
  ioRefSubtreeEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  ioRefVisibleNodes <- newIORef [(Common.Lib.Graph.nodes dGraph)]
  let gid = nextGraphId graphMem -- newIORef (nextGraphId convMaps)
      actGraphInfo = graphInfo graphMem
--  graphId <- newIORef 0
  let gInfo = (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo)
  Result descr _ <- 
    makegraph ("Development graph for "++show ln) 
         -- the global menu
             [GlobalMenu (Menu Nothing
               [Menu (Just "Unnamed nodes")
                 [Button "Hide" 
                          (do --gid <- readIORef graphId
                              Result descr _ <- hideSetOfNodeTypes gid
			                            ["internal",
			                            "locallyEmpty_internal"]
			                            actGraphInfo
                              writeIORef event descr
                              redisplay gid actGraphInfo
                              return ()    ),

                  Button "Show" 
                          (do --gid <- readIORef graphId
			      descr <- readIORef event
                              showIt gid descr actGraphInfo
                              redisplay gid actGraphInfo
                              return ()    )],

	        Menu (Just "Proofs")
                  [Button "Global Subsumption"
			  (proofMenuSef gInfo globSubsume),
		   Button "Local Decomposition (merge of rules)"
			  (proofMenuSef gInfo locDecomp),
		   Button "Global Decomposition"
			  (proofMenuSef gInfo globDecomp)
                    ]])]
      -- the node types
               [("spec", 
		 createLocalMenuNodeTypeSpec "Magenta" convRef dGraph
                              ioRefSubtreeEvents ioRefVisibleNodes
                                  actGraphInfo ioRefGraphMem gInfo
                ),
                ("locallyEmpty_spec", 
		 createLocalMenuNodeTypeSpec "Violet" convRef dGraph
                                          ioRefSubtreeEvents ioRefVisibleNodes
                                          actGraphInfo ioRefGraphMem gInfo),
                ("internal", 
		 createLocalMenuNodeTypeInternal "Grey" convRef dGraph gInfo
                ),
		("locallyEmpty_internal", 
		 createLocalMenuNodeTypeInternal "LightGrey" convRef dGraph gInfo),
                ("dg_ref", 
		 createLocalMenuNodeTypeDgRef "SteelBlue" convRef actGraphInfo 
					      ioRefGraphMem graphMem
                 ),
		("locallyEmpty_dg_ref", 
		 createLocalMenuNodeTypeDgRef "LightSteelBlue" convRef 
		        actGraphInfo ioRefGraphMem graphMem
                 ) ]
      -- the link types
                 [("globaldef",
                   Solid 
		   $$$ createLocalEdgeMenu
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
		  ("def",
                   Solid $$$ Color "Steelblue"
		   $$$ createLocalEdgeMenu
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("proventhm",
                   Solid $$$ Color "Green"
		   $$$ createLocalEdgeMenuThmEdge
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("unproventhm",
                   Solid $$$ Color "Red" 
		   $$$ createLocalEdgeMenuThmEdge
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localproventhm",
                   Dashed $$$ Color "Green" 
		   $$$ createLocalEdgeMenuThmEdge
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localunproventhm",
                   Dashed $$$ Color "Red" 
		   $$$ createLocalEdgeMenuThmEdge
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  -- > ######### welche Farbe fuer reference ##########
                  ("reference",
                   Dotted $$$ Color "Grey"
		   $$$ createLocalEdgeMenu
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue)]
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

--proofMenu :: (ProofStatus -> IO ProofStatus) -> IO ()
proofMenu (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo) proofFun 
  = do
  proofStatus <- readIORef ioRefProofStatus
  Res.Result diags res <- proofFun proofStatus
  case res of
    Nothing -> do sequence $ map (putStrLn . show) diags
                  return ()
    Just newProofStatus@(_,_,history,_) -> do
      writeIORef ioRefProofStatus newProofStatus
      descr <- readIORef event
      convMaps <- readIORef convRef
      --putStrLn (showPretty convMaps "")
      (newDescr,newConvMaps)
         <- applyChanges gid ln actGraphInfo descr convMaps history
      writeIORef event newDescr
      writeIORef convRef newConvMaps
      redisplay gid actGraphInfo
      return ()

proofMenuSef gInfo proofFun =
  proofMenu gInfo (return . return . proofFun)

-- -------------------------------------------------------------
-- methods to create the local menus of the different nodetypes
-- -------------------------------------------------------------

-- local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec color convRef dGraph ioRefSubtreeEvents 
	ioRefVisibleNodes actGraphInfo ioRefGraphMem gInfo =
                 Ellipse $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return s) 
                 $$$ LocalMenu (Menu (Just "node menu")
                   [--createLocalMenuButtonShowSpec convRef dGraph,
		    createLocalMenuButtonShowNumberOfNode,
		    createLocalMenuButtonShowSignature convRef dGraph,
		    createLocalMenuButtonShowTheory gInfo convRef dGraph,
		    createLocalMenuButtonTranslateTheory gInfo convRef dGraph,
		    createLocalMenuButtonShowSublogic convRef dGraph,
                    createLocalMenuButtonShowNodeOrigin convRef dGraph,
                    createLocalMenuButtonProveAtNode gInfo convRef dGraph,
                    createLocalMenuButtonCCCAtNode gInfo convRef dGraph,
		    createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents 
		                     convRef ioRefVisibleNodes ioRefGraphMem
		                                         actGraphInfo,
		    createLocalMenuButtonUndoShowJustSubtree ioRefVisibleNodes 
		              ioRefSubtreeEvents actGraphInfo
		   ]) -- ??? Should be globalized somehow
                  -- >$$$ LocalMenu (Button "xxx" undefined) 
                  $$$ emptyNodeTypeParms 
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal color convRef dGraph gInfo =
                 Ellipse $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return "")
                 $$$ LocalMenu (Menu (Just "node menu")
                    [--createLocalMenuButtonShowSpec convRef dGraph,
		     createLocalMenuButtonShowNumberOfNode,
		     createLocalMenuButtonShowSignature convRef dGraph,
 		     createLocalMenuButtonShowTheory gInfo convRef dGraph,
		     createLocalMenuButtonTranslateTheory gInfo convRef dGraph,
 		     createLocalMenuButtonShowSublogic convRef dGraph,
                     createLocalMenuButtonProveAtNode gInfo convRef dGraph,
                     createLocalMenuButtonCCCAtNode gInfo convRef dGraph,
                     createLocalMenuButtonShowNodeOrigin convRef dGraph])
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef color convRef actGraphInfo 
			     ioRefGraphMem graphMem = 
                 Box $$$ Color color
		 $$$ ValueTitle (\ (s,_,_) -> return s)
		 $$$ LocalMenu (Button "Show referenced library"
		     (\ (name,descr,gid) ->
		        do convMaps <- readIORef convRef
                           --g <- readIORef graphId
		           (refDescr, newGraphInfo, refConvMaps) <- 
		                showReferencedLibrary ioRefGraphMem descr
		                              gid
		                              actGraphInfo
		                              convMaps
		           
--writeIORef convRef newConvMaps
                           writeIORef ioRefGraphMem 
				      graphMem{graphInfo = newGraphInfo, 
					       nextGraphId = refDescr +1}
                           redisplay refDescr newGraphInfo
		          -- redisplay gid graphInfo
		           return ()
		     ))
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)


-- menu button for local menus
createMenuButton title menuFun convRef dGraph =
                    (Button title 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
                           menuFun descr
		                   (abstr2dgNode convMaps)
		                   dGraph
		           return ()
                       )
	            )

createLocalMenuButtonShowSpec = createMenuButton "Show spec" showSpec
createLocalMenuButtonShowSignature = 
  createMenuButton "Show signature" getSignatureOfNode
createLocalMenuButtonShowTheory (proofStatus,_,_,_,_,_) = 
  createMenuButton "Show theory" (getTheoryOfNode proofStatus)
createLocalMenuButtonTranslateTheory (proofStatus,_,_,_,_,_) = 
  createMenuButton "Translate theory" (translateTheoryOfNode proofStatus)
createLocalMenuButtonShowSublogic = 
  createMenuButton "Show sublogic" getSublogicOfNode 
createLocalMenuButtonShowNodeOrigin  = 
  createMenuButton "Show origin" showOriginOfNode 
createLocalMenuButtonProveAtNode gInfo =
  createMenuButton "Prove" (proveAtNode gInfo)
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (cccAtNode gInfo)

createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents convRef 
    ioRefVisibleNodes ioRefGraphMem actGraphInfo = 
                    (Button "Show just subtree"
		      (\ (name,descr,gid) ->
		        do subtreeEvents <- readIORef ioRefSubtreeEvents
		           case Map.lookup descr subtreeEvents of
                             Just _ -> putStrLn 
		               ("it is already just the subtree of node " 
				++ (show descr) ++" shown")
		             Nothing -> 
                               do convMaps <- readIORef convRef
                                  visibleNodes <- readIORef ioRefVisibleNodes
			          (eventDescr,newVisibleNodes,errorMsg) <- 
		                     showJustSubtree ioRefGraphMem
		                           descr gid convMaps visibleNodes
		                  case errorMsg of
		                    Nothing -> do let newSubtreeEvents = 
		                                        Map.insert descr 
		                                            eventDescr 
		                                            subtreeEvents
                                                  writeIORef ioRefSubtreeEvents
		                                      newSubtreeEvents
					          writeIORef ioRefVisibleNodes
		                                      newVisibleNodes
		                                  redisplay gid actGraphInfo
		                                  return()
		                    Just text -> do putStrLn text
		                                    return()
		      )
                    )


createLocalMenuButtonUndoShowJustSubtree ioRefVisibleNodes 
					 ioRefSubtreeEvents actGraphInfo =
                    (Button "Undo show just subtree"
		      (\ (name,descr,gid) ->
		        do visibleNodes <- readIORef ioRefVisibleNodes
                           case (tail visibleNodes) of
                             [] -> do putStrLn 
		                          "Complete graph is already shown"
                                      return()
                             newVisibleNodes@(x:xs) ->
                               do subtreeEvents <- readIORef ioRefSubtreeEvents
                                  case Map.lookup descr subtreeEvents of
                                    Just hide_event -> 
		                      do showIt gid hide_event actGraphInfo
                                         writeIORef ioRefSubtreeEvents 
		                              (Map.delete descr subtreeEvents)
                                         writeIORef ioRefVisibleNodes 
                                               newVisibleNodes
		                         redisplay gid actGraphInfo
		                         return ()
		                    Nothing -> do putStrLn "undo not possible"
		                                  return()
                      )

		    )

-- for debugging
createLocalMenuButtonShowNumberOfNode =
  (Button "Show number of node"
    (\ (name, descr, gid) ->
       getNumberOfNode descr))

-- -------------------------------------------------------------
-- methods to create the local menus for the edges
-- -------------------------------------------------------------
createLocalEdgeMenu = 
    LocalMenu (Menu (Just "edge menu")
	       [createLocalMenuButtonShowMorphismOfEdge,
		createLocalMenuButtonShowOriginOfEdge]
	      )

createLocalEdgeMenuThmEdge =
   LocalMenu (Menu (Just "thm egde menu")
              [createLocalMenuButtonShowMorphismOfEdge,
		createLocalMenuButtonShowOriginOfEdge,
	        createLocalMenuButtonShowProofStatusOfThm]
	      )

createLocalMenuButtonShowMorphismOfEdge = 
  (Button "Show morphism" 
                      (\ (_,descr,maybeLEdge)  -> 
		        do showMorphismOfEdge descr maybeLEdge
		           return ()
                       ))

createLocalMenuButtonShowOriginOfEdge =
    (Button "Show origin"
         (\ (_,descr,maybeLEdge) ->
	   do showOriginOfEdge descr maybeLEdge
	      return ()
	  ))

createLocalMenuButtonShowProofStatusOfThm =
   (Button "Show proof status"
        (\ (_,descr,maybeLEdge) ->
          do showProofStatusOfThm descr maybeLEdge
	     return ()
	 ))
  
-- ------------------------------
-- end of local menu definitions
-- ------------------------------

showSpec descr convMap dgraph =
  case Map.lookup descr convMap of
   Nothing -> return ()
   Just (libname,node) -> do
      let sp = dgToSpec dgraph node
      putStrLn (showPretty sp "")

{- auxiliary method for debugging. shows the number of the given node in the abstraction graph -}
getNumberOfNode :: Descr -> IO()
getNumberOfNode descr =
  let title = "Number of node"
    in createTextDisplay title (showPretty descr "") [size(10,10)]

{- outputs the signature of a node in a window;
used by the node menu defined in initializeGraph-}
getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSignatureOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      do let dgnode = lab' (context node dgraph)
	 case dgnode of
           (DGNode name (G_sign _ sig) _ _) ->
              let title = case name of
                   Nothing -> "Signature"
                   Just n -> "Signature of "++showPretty n ""
               in createTextDisplay title (showPretty sig "") [size(50,50)]
              --putStrLn ((showPretty sig) "\n")
           (DGRef _ _ _) -> error 
			    "nodes of type dg_ref do not have a signature"
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")


{- outputs the theory of a node in a window;
used by the node menu defined in initializeGraph-}
getTheoryOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode -> 
                     DGraph -> IO()
getTheoryOfNode proofStatusRef descr ab2dgNode dgraph = do
 (_,libEnv,_,_) <- readIORef proofStatusRef
 case (do
  (_libname, node) <- 
        Res.maybeToResult nullPos ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode 
  gPair <- computeTheory libEnv dgraph node
  return (node, gPair)
    ) of
  Res.Result [] (Just (n, gp)) ->  
    displayTheory "Theory" n dgraph gp
  Res.Result diags _ -> showDiags defaultHetcatsOpts diags

printTheory :: (G_sign, G_l_sentence_list) -> String
printTheory (G_sign _lid sign, G_l_sentence_list lid' sens) =
   let shownsens = concatMap ((flip shows "\n\n") . 
		    print_named lid' emptyGlobalAnnos) sens
    in showPretty sign "\n\n\n" ++ shownsens

displayTheory :: String -> Node -> DGraph -> (G_sign, G_l_sentence_list) 
	      -> IO ()
displayTheory ext node dgraph gPair =
    let dgnode = lab' (context node dgraph)
        str = printTheory gPair in case dgnode of
           (DGNode name (G_sign _ _) _ _) ->
              let title = case name of
                   Nothing -> ext
                   Just n -> ext ++ " of " ++ showPretty n ""
               in createTextDisplay title str [size(100,50)]
              --putStrLn ((showPretty sig) "\n")
           (DGRef _ _ _) -> error 
			    "nodes of type dg_ref do not have a theory"
     

listBox :: String -> [String] -> IO (Maybe Int)
listBox title entries =
  do
    main <- HTk.createToplevel [HTk.text title]
    lb  <- HTk.newListBox main [HTk.value entries, bg "white", size (25, 25)] ::
             IO (HTk.ListBox String)
    HTk.pack lb [HTk.Side HTk.AtLeft, 
                 HTk.Expand HTk.On, HTk.Fill HTk.Both]
    scb <- HTk.newScrollBar main []
    HTk.pack scb [HTk.Side HTk.AtRight, HTk.Fill HTk.Y]
    lb HTk.# HTk.scrollbar HTk.Vertical scb
    (press, _) <- HTk.bindSimple lb (HTk.ButtonPress (Just 1))
    HTk.sync press
    sel <- HTk.getSelection lb
    HTk.destroy main
    return (case sel of
       Just [i] -> Just i
       _ -> Nothing)

{- translate the theory of a node in a window;
used by the node menu defined in initializeGraph-}
translateTheoryOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode -> 
                     DGraph -> IO()
translateTheoryOfNode proofStatusRef descr ab2dgNode dgraph = do
 (_,libEnv,_,_) <- readIORef proofStatusRef
 case (do
   (_libname, node) <- 
        Res.maybeToResult nullPos ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode 
   th <- computeTheory libEnv dgraph node
   return (node,th) ) of
  Res.Result [] (Just (node,th)) -> do
    Res.Result diags _ <-  Res.ioresToIO(
      do (G_sign lid sign,G_l_sentence_list lid' sens) <- return th
         -- find all comorphism paths starting from lid
         let paths = findComorphismPaths logicGraph (Logic lid)
         -- let the user choose one
         sel <- Res.ioToIORes $ listBox "Choose a logic translation"
                   (map show paths)
         i <- case sel of
           Just j -> return j
           _ -> Res.resToIORes $ Res.fatal_error "" nullPos
         Comorphism cid <- return $ head (drop i paths)
         -- adjust lid's
         let lidS = sourceLogic cid
             lidT = targetLogic cid
         sign' <- Res.resToIORes $ rcoerce lidS lid nullPos sign
         sens' <- Res.resToIORes $ rcoerce lidS lid' nullPos sens
         -- translate theory along chosen comorphism
         (sign'',sens1) <- 
             Res.resToIORes $ Res.maybeToResult 
                                nullPos "Could not map signature"
                        $ map_theory cid (sign',sens')
         let tlog = targetLogic cid
         Res.ioToIORes $ displayTheory "Translated theory" node dgraph 
            (G_sign tlog sign'', G_l_sentence_list tlog sens1)
     )
    showDiags defaultHetcatsOpts diags
    return ()
  Res.Result diags _ -> showDiags defaultHetcatsOpts diags

{- outputs the sublogic of a node in a window;
used by the node menu defined in initializeGraph-}
getSublogicOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSublogicOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      do let dgnode = lab' (context node dgraph)
	 case dgnode of
           (DGNode name _ _ _) ->
	     case (dgn_sign dgnode) of
	       G_sign lid sigma ->
                let logstr = (language_name lid ++ "." 
			      ++ head (sublogic_names lid 
				       (min_sublogic_sign lid sigma)))
                    title = case name of
                     Nothing -> "Sublogic"
                     Just n -> "Sublogic of "++showPretty n ""
                 in createTextDisplay title logstr [size(30,10)]
           (DGRef _ _ _) -> error "nodes of type dg_ref do not have a sublogic"
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")


{- prints the origin of the node -}
showOriginOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
showOriginOfNode descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      do let dgnode = lab' (context node dgraph)
	 case dgnode of
           (DGNode name _ _ orig) ->    
              let title = case name of
                     Nothing -> "Origin of node"
                     Just n -> "Origin of node "++showPretty n ""
               in createTextDisplay title 
                    (showPretty orig "") [size(30,10)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")


{- start local theorem proving at a node -}
--proveAtNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
proveAtNode gInfo@(_,_,convRef,_,_,_) descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just libNode -> 
      do convMaps <- readIORef convRef
         proofMenu gInfo (basicInferenceNode logicGraph libNode)
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")

{- start local consistency checking proving at a node -}
--proveAtNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
cccAtNode gInfo@(_,_,convRef,_,_,_) descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just libNode -> 
      do convMaps <- readIORef convRef
         proofMenu gInfo (basicCCC logicGraph libNode)
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")

{- prints the morphism of the edge -}
showMorphismOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showMorphismOfEdge _ (Just (_,_,linklab)) = 
      createTextDisplay "Signature morphism" 
           (showPretty (dgl_morphism linklab) "") [size(150,50)]
showMorphismOfEdge descr Nothing = 
      createTextDisplay "Error" 
          ("edge "++(show descr)++" has no corresponding edge"
		++ "in the development graph") [size(30,10)]


{- prints the origin of the edge -}
showOriginOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showOriginOfEdge _ (Just (_,_,linklab)) =
      createTextDisplay "Origin of link" 
        (showPretty (dgl_origin linklab) "")  [size(30,10)]
showOriginOfEdge descr Nothing =
      createTextDisplay "Error" 
         ("edge "++(show descr)++" has no corresponding edge"
		++ "in the development graph") [size(30,10)]

{- prints the proof base of the edge -}
showProofStatusOfThm :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showProofStatusOfThm _ (Just ledge) =
    putStrLn (show (getProofStatusOfThm ledge))
showProofStatusOfThm descr Nothing =
    putStrLn ("edge "++(show descr)++" has no corresponding edge"
		++ "in the development graph")


getProofStatusOfThm :: (LEdge DGLinkLab) -> ThmLinkStatus
getProofStatusOfThm (_,_,label) =
  case (dgl_type label) of
    (LocalThm proofStatus _ _) -> proofStatus
    (GlobalThm proofStatus _ _) -> proofStatus
    (HidingThm _ proofStatus) -> proofStatus -- richtig?
--  (FreeThm GMorphism Bool) - keinen proofStatus?
    otherwise -> error "the given edge is not a theorem"

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


{- auxiliar function for convertNodes if the given list of nodes is
emtpy, it returns the conversion maps unchanged otherwise it adds the
converted first node to the abstract graph and to the affected
conversion maps and afterwards calls itself with the remaining node
list -}

convertNodesAux :: ConversionMaps -> Descr -> GraphInfo ->
		     [LNode DGNodeLab] -> LIB_NAME -> IO ConversionMaps
convertNodesAux convMaps descr graphInfo [] libname = return convMaps
convertNodesAux convMaps descr graphInfo ((node,dgnode):lNodes) libname = 
  do nodetype <- (getDGNodeType dgnode)
     Result newDescr err <- addnode descr
			        nodetype
				(getDGNodeName dgnode)
				graphInfo
     --putStrLn (maybe "" id err)
     newConvMaps <- (convertNodesAux
                       convMaps {dg2abstrNode = Map.insert (libname, node) 
				       newDescr (dg2abstrNode convMaps),
                                 abstr2dgNode = Map.insert newDescr 
				      (libname, node) (abstr2dgNode convMaps)}
                                       descr graphInfo lNodes libname)
     return newConvMaps

-- gets the name of a development graph node as a string
						  
getDGNodeName :: DGNodeLab -> String
getDGNodeName dgnode =
  case get_dgn_name dgnode of
    Just simpleId -> tokStr simpleId
    Nothing -> ""

-- gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> IO String
getDGNodeType dgnode =
  do let nodetype = getDGNodeTypeAux dgnode
     case (isDGRef dgnode) of
       True -> return (nodetype++"dg_ref")
       False -> case get_dgn_name dgnode of
                  Just _ -> return (nodetype++"spec")
                  Nothing -> return (nodetype++"internal")
    
getDGNodeTypeAux :: DGNodeLab -> String
getDGNodeTypeAux dgnode = if (locallyEmpty dgnode) then "locallyEmpty_"
                           else ""

getDGLinkType :: DGLinkType -> String
getDGLinkType LocalDef = "def"
getDGLinkType GlobalDef = "globaldef"
getDGLinkType HidingDef = "def"
getDGLinkType (FreeDef _) = "def"
getDGLinkType (CofreeDef _) = "def"
getDGLinkType (LocalThm thmLinkStatus _ _) = 
    "local"++(getThmType thmLinkStatus)
getDGLinkType (GlobalThm thmLinkStatus _ _) = getThmType thmLinkStatus
getDGLinkType (HidingThm _ thmLinkStatus) = getThmType thmLinkStatus
getDGLinkType (FreeThm _ bool) = if bool then "proventhm" else "unproventhm"

getThmType :: ThmLinkStatus -> String
getThmType thmLinkStatus =
  case thmLinkStatus of
    Proven _ -> "proventhm"
    Open -> "unproventhm"

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
invContext :: DGraph -> Node -> Context DGNodeLab DGLinkLab
invContext dgraph node = context node dgraph

{- auxiliar function for convertEges --> not yet implemented! -}
convertEdgesAux :: ConversionMaps -> Descr -> GraphInfo -> 
                    [LEdge DGLinkLab] -> LIB_NAME -> IO ConversionMaps
convertEdgesAux convMaps descr graphInfo [] libname = return convMaps
convertEdgesAux convMaps descr graphInfo ((ledge@(src,tar,edgelab)):lEdges) 
		libname = 
  do let srcnode = Map.lookup (libname,src) (dg2abstrNode convMaps)
         tarnode = Map.lookup (libname,tar) (dg2abstrNode convMaps)
     case (srcnode,tarnode) of 
      (Just s, Just t) -> do
        Result newDescr err <- addlink descr (getDGLinkType (dgl_type edgelab))
                                   "" (Just ledge) s t graphInfo
        newConvMaps <- (convertEdgesAux
                       convMaps {dg2abstrEdge = Map.insert
				     (libname, (src,tar,show edgelab))
				     newDescr
				     (dg2abstrEdge convMaps),
                                 abstr2dgEdge = Map.insert newDescr
		                     (libname, (src,tar,show edgelab))
		                     (abstr2dgEdge convMaps)}
                                         descr graphInfo lEdges libname)
        return newConvMaps
      otherwise -> error "Cannot find nodes"


showReferencedLibrary :: IORef GraphMem -> Descr -> Descr -> GraphInfo 
	      -> ConversionMaps -> IO (Descr, GraphInfo, ConversionMaps)
showReferencedLibrary graphMem descr abstractGraph graphInfo convMaps =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,node) -> 
         case Map.lookup libname libname2dgMap of
	  Just (_,_,dgraph) -> 
            do let (_,(DGRef _ refLibname refNode)) = 
		       labNode' (context node dgraph)
	       case Map.lookup refLibname libname2dgMap of
                 Just (_,refDgraph,_) -> 
		     convertGraph graphMem refLibname (libname2dg convMaps)
		 Nothing -> error ("The referenced library ("
				     ++ (show refLibname)
				     ++ ") is unknown")
          Nothing ->
	    error ("Selected node belongs to unknown library: " 
		   ++ (show libname))
    Nothing ->
      error ("there is no node with the descriptor "
	         ++ show descr)

    where libname2dgMap = libname2dg convMaps

-- --------------------------
-- returntype festlegen
showJustSubtree:: IORef GraphMem -> Descr -> Descr -> ConversionMaps 
	       -> [[Node]]-> IO (Descr, [[Node]], Maybe String)
showJustSubtree ioRefGraphMem descr abstractGraph convMaps visibleNodes =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,parentNode) ->
      case Map.lookup libname libname2dgMap of
	Just (_,_,dgraph) -> 
	  do let -- allDgNodes = Common.Lib.Graph.nodes dgraph
                 allNodes = getNodeDescriptors (head visibleNodes) 
			    libname convMaps -- allDgNodes libname convMaps
                 dgNodesOfSubtree = nub (parentNode:(getNodesOfSubtree dgraph 
						     visibleNodes parentNode))
                 -- the selected node (parentNode) shall not be hidden either,
                 -- and we already know its descriptor (descr)
		 nodesOfSubtree = getNodeDescriptors dgNodesOfSubtree 
				  libname convMaps
	         nodesToHide = filter (notElemR nodesOfSubtree) allNodes
	     graphMem <- readIORef ioRefGraphMem
	     (Result eventDescr errorMsg) <- hidenodes abstractGraph 
					     nodesToHide (graphInfo graphMem)
	     return (eventDescr, (dgNodesOfSubtree:visibleNodes), errorMsg)
{-	     case errorMsg of 
	       Just text -> return (-1,text)
	       Nothing -> return (eventDescr,
			  return convMaps-}
        Nothing -> error 
	  ("showJustSubtree: Selected node belongs to unknown library: " 
	   ++ (show libname))
    Nothing ->
      error ("showJustSubtree: there is no node with the descriptor "
	         ++ show descr)

    where libname2dgMap = libname2dg convMaps



getNodeDescriptors :: [Node] -> LIB_NAME -> ConversionMaps -> [Descr]
getNodeDescriptors [] _ _ = []
getNodeDescriptors (node:nodelist) libname convMaps =
  case Map.lookup (libname,node) (dg2abstrNode convMaps) of
    Just descr -> descr:(getNodeDescriptors nodelist libname convMaps)
    Nothing -> error ("getNodeDescriptors: There is no descriptor for dgnode " 
		      ++ (show node))


getNodesOfSubtree :: DGraph -> [[Node]] -> Node -> [Node]
getNodesOfSubtree dgraph visibleNodes node = 
    (concat (map (getNodesOfSubtree dgraph visibleNodes) predOfNode))
    ++predOfNode
    where predOfNode = filter (elemR (head visibleNodes)) (pre dgraph node)

elemR :: Eq a => [a] -> a -> Bool
elemR list element = elem element list

notElemR :: Eq a => [a] -> a -> Bool
notElemR list element = notElem element list



-- -- ################ einbindung von proofs.hs ############
applyChanges :: Descr -> LIB_NAME -> GraphInfo -> Descr -> ConversionMaps
	          -> [([DGRule],[DGChange])]
		  -> IO (Descr, ConversionMaps)
applyChanges gid libname graphInfo eventDescr convMaps history =
  case history of
    [] -> return (eventDescr, convMaps)
    (historyElem:list) ->
      case snd historyElem of
	[] -> return (eventDescr, convMaps)
	changes@(x:xs) -> 
          applyChangesAux gid libname graphInfo eventDescr convMaps changes

applyChangesAux :: Descr -> LIB_NAME -> GraphInfo -> Descr
		  -> ConversionMaps -> [DGChange]
	          -> IO (Descr, ConversionMaps)
applyChangesAux _ _ _ eventDescr convMaps [] = return (eventDescr+1, convMaps)
applyChangesAux gid libname graphInfo eventDescr convMaps (change:changes) =
  case change of
    InsertNode lNode -> error "insert node not yet implemented"
    DeleteNode node -> error "delete node not yet implemented"
    InsertEdge ledge@(src,tgt,edgelab) -> 
      do let dg2abstrNodeMap = dg2abstrNode convMaps
         case (Map.lookup (libname,src) dg2abstrNodeMap,
	       Map.lookup (libname,tgt) dg2abstrNodeMap) of
           (Just abstrSrc, Just abstrTgt) ->
             do let dgEdge = (libname, (src,tgt,show edgelab))
	        (Result descr err) <- 
                   addlink gid (getDGLinkType (dgl_type edgelab))
			      "" (Just ledge) abstrSrc abstrTgt graphInfo
	        case err of
	          Nothing ->
	            do let newConvMaps = convMaps 
                              {dg2abstrEdge =
		               Map.insert dgEdge descr (dg2abstrEdge convMaps),
	                       abstr2dgEdge =
		               Map.insert descr dgEdge (abstr2dgEdge convMaps)}
                       applyChangesAux gid libname graphInfo (descr+1)
			 	 newConvMaps changes
	          Just _ -> 
-- -- ##### was machen, wenn Einfügen nicht erfolgreich?! ###
-- Momentane Lösung: ignorieren...
	           applyChangesAux gid libname graphInfo eventDescr
			         convMaps changes
           otherwise -> 
-- -- ##### was machen, wenn Einfügen nicht erfolgreich?! ###
-- Momentane Lösung: ignorieren...
	     applyChangesAux gid libname graphInfo eventDescr
		 	         convMaps changes
   

    DeleteEdge (src,tgt,edgelab) -> 
      do let dgEdge = (libname, (src,tgt,show edgelab))
             dg2abstrEdgeMap = dg2abstrEdge convMaps 
         case Map.lookup dgEdge dg2abstrEdgeMap of
            Just abstrEdge ->
              do (Result descr err) <- dellink gid abstrEdge graphInfo
		 case err of
	           Nothing -> 
		     do let newConvMaps = convMaps 
		                {dg2abstrEdge =
				     Map.delete dgEdge dg2abstrEdgeMap,
				 abstr2dgEdge = 
				     Map.delete abstrEdge (abstr2dgEdge 
							   convMaps)}
 		        applyChangesAux gid libname graphInfo (descr+1)
				 newConvMaps changes
-- -- @@@ was machen, wenn Entfernen nicht erfolgreich?! @@@
-- Momentane Lösung: abbrechen...
 		   Just _ -> error ("applyChangesAux: could not delete edge "
			         ++ (show abstrEdge))

	    Nothing -> error ("applyChangesAux: deleted edge from " 
			      ++ (show src) ++ " to " ++ (show tgt) 
			      ++ " of type " ++ (show (dgl_type edgelab))
			      ++ " and origin " ++ (show (dgl_origin edgelab))
			      ++ " of development "
                         ++ "graph does not exist in abstraction graph" {- ++ (showPretty convMaps "\n") -})
