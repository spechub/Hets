{-
Module      :  $Header$
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

   Conversion of development graphs from Logic.DevGraph
   to abstract graphs of the graph display interface
-}

{-
   todo:
   hiding of internal nodes:
    internal nodes that are not between named nodes should be kept
   display inclusions and inter-logic links in special colour
   try different graph layout algorithms for daVinci (dot?)
   close program when all windows are closed
   issue warning when theory cannot be flattened
   different linktypes for local and hiding definition links
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
import GUI.HTkUtils
import DaVinciGraph
import GraphDisp
import GraphConfigure
import TextDisplay
import Configuration
import qualified HTk

import qualified Common.Lib.Map as Map
import Common.Lib.Graph
import Common.Id
import Common.Lib.Pretty as Pretty hiding (isEmpty)
import Common.PrettyPrint
import qualified Common.Result as Res
import Syntax.AS_Library
import Common.GlobalAnnotations

import Driver.Options
import Driver.WriteFn
import Driver.ReadFn
import FileDialog
import Events
import System.Directory
import Broadcaster(newSimpleBroadcaster,applySimpleUpdate)
import Sources(toSimpleSource)

import Data.IORef
import Data.Maybe
import List(nub)
import Control.Monad

import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)

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


data InternalNames = 
     InternalNames { showNames :: Bool,
                     updater :: [(String,(String -> String) -> IO ())] }
 

type GInfo = (IORef ProofStatus,
              IORef Descr,
              IORef ConversionMaps,
              Descr,
              LIB_NAME,
              GraphInfo,
              IORef InternalNames, -- show internal names?
              HetcatsOpts,
	      IORef [[Node]]
	     )

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

convertGraph :: IORef GraphMem -> LIB_NAME -> LibEnv -> HetcatsOpts
	     -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph graphMem libname libEnv hetsOpts =
  do --nextGraphId <- newIORef 0
     let convMaps = ConversionMaps
           {dg2abstrNode = Map.empty::DGraphToAGraphNode, 
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,
            libname2dg = libEnv}

     case Map.lookup libname libEnv of

       Just globContext@(_,_,dgraph) -> 
	do (abstractGraph,graphInfo,convRef) <-
	          initializeGraph graphMem libname dgraph convMaps globContext hetsOpts
	   if (isEmpty dgraph) then 
                return (abstractGraph, graphInfo,convMaps)
            else 
	     do newConvMaps <- convertNodes convMaps abstractGraph
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
                     -> GlobalContext -> HetcatsOpts
		     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ioRefGraphMem ln dGraph convMaps globContext hetsOpts = do 
  graphMem <- readIORef ioRefGraphMem
  event <- newIORef 0
  convRef <- newIORef convMaps
  showInternalNames <- newIORef (InternalNames False [])
  ioRefProofStatus <- newIORef (globContext, libname2dg convMaps,
		                [([]::[DGRule], []::[DGChange])],
				dGraph)
  ioRefSubtreeEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  ioRefVisibleNodes <- newIORef [(Common.Lib.Graph.nodes dGraph)]
  let gid = nextGraphId graphMem -- newIORef (nextGraphId convMaps)
      actGraphInfo = graphInfo graphMem
--  graphId <- newIORef 0
  let gInfo = (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo, showInternalNames, hetsOpts, ioRefVisibleNodes)
  Result descr _ <- 
    makegraph ("Development graph for "++show ln) 
         -- action on "open"
             (do currentPath <- getCurrentDirectory
	         event <- fileDialogStr "Open..." currentPath
	         maybeFilePath <- sync event
                 case maybeFilePath of
	           Just filePath ->
	             do openProofStatus filePath ioRefProofStatus convRef hetsOpts
                   Nothing ->
	             do error ("Could not open file.")
              )
         -- action on "save"
             (do proofStatus <- readIORef ioRefProofStatus
                 writeShATermFile ("./" ++ (show ln) ++ ".log") proofStatus)
         -- action on "save as...:"
             (do currentPath <- getCurrentDirectory
	         event <- newFileDialogStr "Save as..." currentPath
                 maybeFilePath <- sync event
                 case maybeFilePath of
	           Just filePath -> do
                     proofStatus <- readIORef ioRefProofStatus
                     writeShATermFile filePath proofStatus
	           Nothing ->
                     do error ("Could not save file.")
              )
         -- the global menu
             [GlobalMenu (Menu Nothing
               [Menu (Just "Unnamed nodes")
                 [Button "Hide/show names" 
                          (do (int::InternalNames) <- readIORef showInternalNames
                              let showThem = not $ showNames int
                                  showIt s = if showThem then s else ""
                              mapM_ (\(s,upd) -> upd (\_ -> showIt s)) (updater int)
                              writeIORef showInternalNames (int {showNames = showThem})
                              redisplay gid actGraphInfo
                              return ()    ),
                  Button "Hide nodes" 
                          (do --gid <- readIORef graphId
                              Result descr _ <- hideSetOfNodeTypes gid
			                            ["internal",
			                            "locallyEmpty_internal"]
			                            actGraphInfo
                              writeIORef event descr
                              redisplay gid actGraphInfo
                              return ()    ),

                  Button "Show nodes" 
                          (do --gid <- readIORef graphId
			      descr <- readIORef event
                              showIt gid descr actGraphInfo
                              redisplay gid actGraphInfo
                              return ()    )],

	        Menu (Just "Proofs")
                  [Button "Automatic"
			  (proofMenu gInfo (fmap return . automatic)),
                   Button "Global Subsumption"
			  (proofMenuSef gInfo globSubsume),
		   Button "Global Decomposition"
			  (proofMenuSef gInfo globDecomp),
		   Button "Local Subsumption"
		          (proofMenuSef gInfo locSubsume),
		   Button "Local Decomposition (merge of rules)"
			  (proofMenuSef gInfo locDecomp),
		   Button "Hide Theorem Shift"
	                  (proofMenu gInfo (fmap return . 
					    (hideTheoremShift False))),
		   Button "Theorem Hide Shift"
	                  (proofMenu gInfo (fmap return . theoremHideShift))
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
					      ioRefGraphMem graphMem gInfo
                 ),
		("locallyEmpty_dg_ref", 
		 createLocalMenuNodeTypeDgRef "LightSteelBlue" convRef 
		        actGraphInfo ioRefGraphMem graphMem gInfo
                 ) ]
      -- the link types
                 [("globaldef",
                   Solid 
		   $$$ createLocalEdgeMenu gInfo
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
		  ("def",
                   Solid $$$ Color "Steelblue"
		   $$$ createLocalEdgeMenu gInfo
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
		  ("hidingdef",
                   Solid $$$ Color "Lightblue"
		   $$$ createLocalEdgeMenu gInfo
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
		  ("hetdef",
                   GraphConfigure.Double
		   $$$ createLocalEdgeMenu gInfo
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("proventhm",
                   Solid $$$ Color "Green"
		   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("unproventhm",
                   Solid $$$ Color "Red" 
		   $$$ createLocalEdgeMenuThmEdge gInfo
		   $$$ createLocalMenuValueTitleShowConservativity
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localproventhm",
                   Dashed $$$ Color "Green" 
		   $$$ createLocalEdgeMenuThmEdge gInfo
		   $$$ createLocalMenuValueTitleShowConservativity
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localunproventhm",
                   Dashed $$$ Color "Red" 
		   $$$ createLocalEdgeMenuThmEdge gInfo
		   $$$ createLocalMenuValueTitleShowConservativity
		   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("unprovenhidingthm",
                   Solid $$$ Color "Orange"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("provenhidingthm",
                   Solid $$$ Color "Lightgreen"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  -- > ######### welche Farbe fuer reference ##########
                  ("reference",
                   Dotted $$$ Color "Grey"
		   $$$ createLocalEdgeMenu gInfo
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue)]
                 [("globaldef","globaldef","globaldef"),
		  ("globaldef","def","def"),
		  ("globaldef","hetdef","hetdef"),
                  ("globaldef","proventhm","proventhm"),
                  ("globaldef","unproventhm","unproventhm"),
                  ("globaldef","localunproventhm","localunproventhm"),
		  ("def","globaldef","def"),
		  ("def","def","def"),
		  ("def","hetdef","hetdef"),
                  ("def","proventhm","proventhm"),
                  ("def","unproventhm","unproventhm"),
                  ("def","localunproventhm","localunproventhm"),
		  ("hetdef","globaldef","hetdef"),
		  ("hetdef","def","hetdef"),
		  ("hetdef","hetdef","hetdef"),
                  ("hetdef","proventhm","proventhm"),
                  ("hetdef","unproventhm","unproventhm"),
                  ("hetdef","localunproventhm","localunproventhm"),
                  ("proventhm","globaldef","proventhm"),
                  ("proventhm","def","proventhm"),
                  ("proventhm","hetdef","proventhm"),
                  ("proventhm","proventhm","proventhm"),
                  ("proventhm","unproventhm","unproventhm"),
                  ("proventhm","localunproventhm","localunproventhm"),
                  ("unproventhm","globaldef","unproventhm"),
                  ("unproventhm","def","unproventhm"),
                  ("unproventhm","hetdef","unproventhm"),
                  ("unproventhm","proventhm","unproventhm"),
                  ("unproventhm","unproventhm","unproventhm"), 
                  ("unproventhm","localunproventhm","localunproventhm"), 
                  ("localunproventhm","globaldef","localunproventhm"),
                  ("localunproventhm","def","localunproventhm"),
                  ("localunproventhm","hetdef","localunproventhm"),
                  ("localunproventhm","proventhm","localunproventhm"),
                  ("localunproventhm","unproventhm","localunproventhm"), 
                  ("localunproventhm","localunproventhm","localunproventhm")] 
                 actGraphInfo
  writeIORef ioRefGraphMem graphMem{nextGraphId = gid+1}
  graphMem'<- readIORef ioRefGraphMem
  return (descr,graphInfo graphMem',convRef)


openProofStatus :: FilePath -> (IORef ProofStatus) -> (IORef ConversionMaps)
		-> HetcatsOpts -> IO()
openProofStatus filename ioRefProofStatus convRef hetsOpts =
  do resultProofStatus <- proofStatusFromShATerm filename
     case Res.maybeResult resultProofStatus of
       Nothing -> error ("Could not read proof status from file '" 
                         ++ (show filename) ++ "'")
       Just proofStatus@(globCon,libEnv',_,_) ->
         do writeIORef ioRefProofStatus proofStatus
            initGraphInfo <- initgraphs
            graphMem' <- (newIORef GraphMem{nextGraphId = 0, 
				      graphInfo = initGraphInfo})
	    let lns = [ln|(ln,gc) <- Map.assocs libEnv', gc == globCon]
	    case length lns of
              1 -> do let libname = head lns
                      (gid, actGraphInfo, convMaps) 
			  <- convertGraph graphMem' libname libEnv' hetsOpts
                      writeIORef convRef convMaps
                      redisplay gid actGraphInfo
		      return ()
              _ -> error "Could not determine libname of the saved development graph"
                                  
proofMenu :: GInfo
             -> (ProofStatus -> IO (Res.Result ProofStatus))
             -> IO ()
proofMenu (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo, _, _, ioRefVisibleNodes) proofFun 
  = do
  proofStatus <- readIORef ioRefProofStatus
  Res.Result diags res <- proofFun proofStatus
  case res of
    Nothing -> do sequence $ map (putStrLn . show) diags
                  return ()
    Just newProofStatus@((globAnnos,globEnv,_),libEnv,history,dgraph) -> do
      let newGlobContext = (globAnnos,globEnv,dgraph)
          newLibEnv = Map.insert ln newGlobContext libEnv
      writeIORef ioRefProofStatus (newGlobContext, newLibEnv, history,dgraph)
      descr <- readIORef event
      convMaps <- readIORef convRef
      --putStrLn (showPretty convMaps "")
      (newDescr,convMapsAux)
         <- applyChanges gid ln actGraphInfo descr ioRefVisibleNodes
	    convMaps history
      let newConvMaps = 
	      convMapsAux {libname2dg =
			Map.insert ln newGlobContext (libname2dg convMapsAux)}
      writeIORef event newDescr
      writeIORef convRef newConvMaps
      redisplay gid actGraphInfo
      return ()

proofMenuSef :: GInfo
             -> (ProofStatus -> ProofStatus)
             -> IO ()
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
		    createLocalMenuButtonShowSignature gInfo,
		    createLocalMenuButtonShowTheory gInfo,
		    createLocalMenuButtonTranslateTheory gInfo,
		    createLocalMenuTaxonomy gInfo convRef dGraph,
		    createLocalMenuButtonShowSublogic gInfo,
                    createLocalMenuButtonShowNodeOrigin gInfo,
                    createLocalMenuButtonProveAtNode gInfo,
                    createLocalMenuButtonCCCAtNode gInfo,
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
createLocalMenuNodeTypeInternal color convRef dGraph 
                                gInfo@(_,_,_,_,_,_,showInternalNames,_,_) =
                 Ellipse $$$ Color color
		 $$$ ValueTitleSource (\ (s,_,_) -> do
                       b <- newSimpleBroadcaster ""
                       int <- readIORef showInternalNames
                       let upd = (s,applySimpleUpdate b)
                       writeIORef showInternalNames (int {updater = upd:updater int})
                       return $ toSimpleSource b)
                 $$$ LocalMenu (Menu (Just "node menu")
                    [--createLocalMenuButtonShowSpec convRef dGraph,
		     createLocalMenuButtonShowNumberOfNode,
		     createLocalMenuButtonShowSignature gInfo,
 		     createLocalMenuButtonShowTheory gInfo,
		     createLocalMenuButtonTranslateTheory gInfo,
		     createLocalMenuTaxonomy gInfo convRef dGraph,
 		     createLocalMenuButtonShowSublogic gInfo,
                     createLocalMenuButtonProveAtNode gInfo,
                     createLocalMenuButtonCCCAtNode gInfo,
                     createLocalMenuButtonShowNodeOrigin gInfo])
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef color convRef actGraphInfo 
			     ioRefGraphMem graphMem (_,_,_,_,_,_,_,hetsOpts,_) = 
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
		                              hetsOpts
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
createMenuButtonGInfo title menuFun 
		      (ioProofStatus,_,convRef,_,_,_,_,_,_) =
                    (Button title 
                      (\ (name,descr,gid) ->
                        do convMaps <- readIORef convRef
		           (_,_,_,dGraph) <- readIORef ioProofStatus
                           menuFun descr
		                   (abstr2dgNode convMaps)
		                   dGraph
		           return ()
                       )
	            )

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
  createMenuButtonGInfo "Show signature" getSignatureOfNode
createLocalMenuButtonShowTheory gInfo = 
  createMenuButtonGInfo "Show theory" (getTheoryOfNode gInfo) gInfo
createLocalMenuButtonTranslateTheory gInfo = 
  createMenuButtonGInfo "Translate theory" (translateTheoryOfNode gInfo) gInfo


{- | 
   create a sub Menu for taxonomy visualisation
   (added by KL)
-}
--createLocalMenuTaxonomy :: IORef ProofStatus -> Descr -> AGraphToDGraphNode -> 
--                     DGraph -> IO ()
createLocalMenuTaxonomy (proofStatus,_,_,_,_,_,_,_,_) convRef dGraph =
      (Menu (Just "Taxonomy graphs")
       [createMenuButton "Subsort graph" 
	       (passTh displaySubsortGraph) convRef dGraph,
	createMenuButton "Concept graph"
	       (passTh displayConceptGraph) convRef dGraph])
    where passTh displayFun descr ab2dgNode dgraph =
	      do r <- lookupTheoryOfNode proofStatus 
                                         descr ab2dgNode dgraph
		 case r of
		  Res.Result [] (Just (n, gth)) -> 
		      displayFun (showPretty n "") gth
		  Res.Result diags _ -> 
		     showDiags defaultHetcatsOpts diags
 


createLocalMenuButtonShowSublogic gInfo@(proofStatus,_,_,_,_,_,_,_,_) = 
  createMenuButtonGInfo "Show sublogic" (getSublogicOfNode proofStatus) gInfo
createLocalMenuButtonShowNodeOrigin  = 
  createMenuButtonGInfo "Show origin" showOriginOfNode 
createLocalMenuButtonProveAtNode gInfo =
  createMenuButtonGInfo "Prove" (proveAtNode False gInfo) gInfo
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButtonGInfo "Check consistency" (proveAtNode True gInfo) gInfo


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
createLocalEdgeMenu gInfo = 
    LocalMenu (Menu (Just "edge menu")
	       [createLocalMenuButtonShowMorphismOfEdge gInfo,
		createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonCheckconsistencyOfEdge gInfo]
	      )

createLocalEdgeMenuThmEdge gInfo =
   LocalMenu (Menu (Just "thm egde menu")
              [createLocalMenuButtonShowMorphismOfEdge gInfo,
		createLocalMenuButtonShowOriginOfEdge gInfo,
	        createLocalMenuButtonShowProofStatusOfThm gInfo,
                createLocalMenuButtonCheckconsistencyOfEdge gInfo]
	      )

createLocalMenuButtonShowMorphismOfEdge _ = 
  (Button "Show morphism" 
                      (\ (_,descr,maybeLEdge)  -> 
		        do showMorphismOfEdge descr maybeLEdge
		           return ()
                       ))

createLocalMenuButtonShowOriginOfEdge _ =
    (Button "Show origin"
         (\ (_,descr,maybeLEdge) ->
	   do showOriginOfEdge descr maybeLEdge
	      return ()
	  ))

createLocalMenuButtonCheckconsistencyOfEdge gInfo = 
  (Button "Check conservativity (preliminary)" 
                      (\ (ginfo,descr,maybeLEdge)  -> 
		        do checkconsistencyOfEdge descr gInfo maybeLEdge
		           return ()
                       ))

createLocalMenuButtonShowProofStatusOfThm _ =
   (Button "Show proof status"
        (\ (_,descr,maybeLEdge) ->
          do showProofStatusOfThm descr maybeLEdge
	     return ()
	 ))

createLocalMenuValueTitleShowConservativity =
   (ValueTitle 
      (\ (_,_,maybeLEdge) ->
        case maybeLEdge of
          Just (_,_,edgelab) ->
            case dgl_type edgelab of
                        GlobalThm _ c status -> return (showCons c status)
                        LocalThm _ c status -> return (showCons c status)
                        _ -> return ""
          Nothing -> return ""
              ))
  where
    showCons :: Conservativity -> ThmLinkStatus -> String
    showCons c status =
      case (c,status) of
        (None,_) -> show c
        (_,Open) -> (show c) ++ "?"
        _ -> show c

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
           (DGNode name (G_sign _ sig) _ _ _ _) ->
              let title = "Signature of "++showName name
               in createTextDisplay title (showPretty sig "") [size(80,50)]
              --putStrLn ((showPretty sig) "\n")
           (DGRef _ _ _) -> error 
			    "nodes of type dg_ref do not have a signature"
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")

{- | 
   fetches the theory from a node inside the IO Monad  
   (added by KL based on code in getTheoryOfNode) -}
lookupTheoryOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode -> 
                      DGraph -> IO (Res.Result (Node,G_theory))
lookupTheoryOfNode proofStatusRef descr ab2dgNode dgraph = do
 (_,libEnv,_,_) <- readIORef proofStatusRef
 case (do
  (_libname, node) <- 
        Res.maybeToResult nullPos ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode 
  gth <- computeTheory libEnv dgraph node
  return (node, gth)
    ) of
   r -> return r

{- outputs the theory of a node in a window;
used by the node menu defined in initializeGraph-}
getTheoryOfNode :: GInfo -> Descr -> AGraphToDGraphNode -> 
                     DGraph -> IO()
getTheoryOfNode  (proofStatusRef,_,_,_,_,_,_,hetsOpts,_) descr ab2dgNode dgraph = do
 r <- lookupTheoryOfNode proofStatusRef descr ab2dgNode dgraph
 case r of
  Res.Result diags res -> do
    showDiags hetsOpts diags
    case res of
      (Just (n, gth)) -> displayTheory "Theory" n dgraph gth
      _ -> return ()

printTheory :: G_theory -> String
printTheory (G_theory lid sign sens) =
   let shownsens = concatMap ((flip shows "\n\n") . 
		    print_named lid emptyGlobalAnnos) sens
    in showPretty sign "\n\n\n" ++ shownsens

displayTheory :: String -> Node -> DGraph -> G_theory
	      -> IO ()
displayTheory ext node dgraph gth =
    let dgnode = lab' (context node dgraph)
        str = printTheory (simplifyTh gth) in case dgnode of
           (DGNode name (G_sign _ _) _ _ _ _) ->
              let thname = showName name
                  title = ext ++ " of " ++ thname
               in createTextSaveDisplay title (thname++".het") str [size(100,50)]
              --putStrLn ((showPretty sig) "\n")
           (DGRef _ _ _) -> error 
			    "nodes of type dg_ref do not have a theory"
     


{- translate the theory of a node in a window;
used by the node menu defined in initializeGraph-}
translateTheoryOfNode :: GInfo -> Descr -> AGraphToDGraphNode -> 
                     DGraph -> IO()
translateTheoryOfNode gInfo@(proofStatusRef,_,_,_,_,_,_,opts,_) descr ab2dgNode dgraph = do
 (_,libEnv,_,_) <- readIORef proofStatusRef
 case (do
   (_libname, node) <- 
        Res.maybeToResult nullPos ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode 
   th <- computeTheory libEnv dgraph node
   return (node,th) ) of
  Res.Result [] (Just (node,th)) -> do
    Res.Result diags _ <-  Res.ioresToIO(
      do G_theory lid sign sens <- return th
         -- find all comorphism paths starting from lid
         let paths = findComorphismPaths logicGraph (sublogicOfTh th)
         -- let the user choose one
         sel <- Res.ioToIORes $ listBox "Choose a logic translation"
                   (map show paths)
         i <- case sel of
           Just j -> return j
           _ -> Res.resToIORes $ Res.fatal_error "" nullPos
         Comorphism cid <- return (paths!!i)
         -- adjust lid's
         let lidS = sourceLogic cid
             lidT = targetLogic cid
         sign' <- coerce lidS lid sign
         sens' <- coerce lidS lid sens
         -- translate theory along chosen comorphism
         (sign'',sens1) <- 
             Res.resToIORes $ map_theory cid (sign',sens')
         Res.ioToIORes $ displayTheory "Translated theory" node dgraph 
            (G_theory lidT sign'' sens1)
     )
    showDiags opts diags
    return ()
  Res.Result diags _ -> showDiags opts diags

{- outputs the sublogic of a node in a window;
used by the node menu defined in initializeGraph-}
getSublogicOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSublogicOfNode proofStatusRef descr ab2dgNode dgraph = do
  (_,libEnv,_,_) <- readIORef proofStatusRef
  case Map.lookup descr ab2dgNode of
    Just (libname, node) -> 
      let dgnode = lab' (context node dgraph)
          name = case dgnode of
                       (DGNode name _ _ _ _ _) -> name
                       _ -> emptyName
       in case computeTheory libEnv dgraph node of
        Res.Result _ (Just th) ->
                let logstr = show $ sublogicOfTh th
                    title =  "Sublogic of "++showName name
                 in createTextDisplay title logstr [size(30,10)]
        Res.Result diags _ -> 
          error ("Could not compute theory for sublogic computation: "++
                concatMap show diags)
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
           (DGNode name _ _ _ _ orig) ->    
              let title =  "Origin of node "++showName name
               in createTextDisplay title 
                    (showPretty orig "") [size(30,10)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")


{- start local theorem proving or consistency checking at a node -}
--proveAtNode :: Bool -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
proveAtNode checkCons gInfo@(_,_,convRef,_,_,_,_,_,_) descr ab2dgNode dgraph = 
  case Map.lookup descr ab2dgNode of
    Just libNode -> 
      do convMaps <- readIORef convRef
         proofMenu gInfo (basicInferenceNode checkCons logicGraph libNode)
    Nothing -> error ("node with descriptor "
                      ++ (show descr) 
                      ++ " has no corresponding node in the development graph")


{- prints the morphism of the edge -}
showMorphismOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showMorphismOfEdge _ (Just (_,_,linklab)) = 
      createTextDisplay "Signature morphism" 
           ((showPretty (dgl_morphism linklab) "")++hidingMorph) [size(150,50)]
  where
    hidingMorph = case (dgl_type linklab) of
		    (HidingThm morph _) -> "\n ++++++ \n"
					   ++ (showPretty morph "")
                    _ -> ""
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
    createTextDisplay "Proof Status" 
         (show (getProofStatusOfThm ledge)) [size(30,10)]
showProofStatusOfThm descr Nothing =
    putStrLn ("edge "++(show descr)++" has no corresponding edge"
		++ "in the development graph")

{- check consistency of the edge -}
checkconsistencyOfEdge :: Descr -> GInfo -> Maybe (LEdge DGLinkLab) -> IO()
checkconsistencyOfEdge _ (ref,_,_,_,_,_,_,opts,_) (Just (source,target,linklab)) = do 
  (_,libEnv,_,dgraph) <- readIORef ref
  let dgtar = lab' (context target dgraph)
  case dgtar of
    (DGNode name _ (G_l_sentence_list lid sens) _ _ _) -> do   
      GMorphism cid sign1 morphism2 <- return $ dgl_morphism linklab
      let morphism2' = case coerce (targetLogic cid) lid morphism2 of
           Just m -> m
           _ -> error "checkconsistencyOfEdge: wrong logic"
      let th = case computeTheory libEnv dgraph source of
                Res.Result _ (Just th1) -> th1
                _ -> error "checkconsistencyOfEdge: computeTheory"
      G_theory lid1 sign1 sens1 <- return th
      case coerce lid1 lid (sign1,sens1) of
           Just (sign2, sens2) -> 
             let Res.Result diags res = consCheck lid (sign2,sens2) morphism2' sens
                 showRes = case res of
                   Just(Just True) -> "The link is conservative"
                   Just(Just False) -> "The link is not conservative"
                   _ -> "Could not determine whether link is conservative"
                 showDiags = unlines (map show diags)
              in createTextDisplay "Result of consistency check" 
                      (showRes++"\n"++showDiags) [size(50,50)]
           _ -> error "checkconsistencyOfEdge: wrong logic"   

checkconsistencyOfEdge descr _ Nothing = 
      createTextDisplay "Error" 
          ("edge "++(show descr)++" has no corresponding edge"
		++ "in the development graph") [size(30,10)]


getProofStatusOfThm :: (LEdge DGLinkLab) -> ThmLinkStatus
getProofStatusOfThm (_,_,label) =
  case (dgl_type label) of
    (LocalThm proofStatus _ _) -> proofStatus
    (GlobalThm proofStatus _ _) -> proofStatus
    (HidingThm _ proofStatus) -> proofStatus -- richtig?
--  (FreeThm GMorphism Bool) - keinen proofStatus?
    _ -> error "the given edge is not a theorem"

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



-- gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> IO String
getDGNodeType dgnode =
  do let nodetype = getDGNodeTypeAux dgnode
     case (isDGRef dgnode) of
       True -> return (nodetype++"dg_ref")
       False -> if isInternalNode dgnode 
                   then return (nodetype++"internal")
                   else return (nodetype++"spec")
    
getDGNodeTypeAux :: DGNodeLab -> String
getDGNodeTypeAux dgnode = if (locallyEmpty dgnode) then "locallyEmpty_"
                           else ""

getDGLinkType :: DGLinkLab -> String
getDGLinkType lnk = case (dgl_type lnk) of
  GlobalDef ->
    if hasIdComorphism $ dgl_morphism lnk then "globaldef"
        else "hetdef"
  t -> getDGLinkTypeAux t

getDGLinkTypeAux :: DGLinkType -> String
getDGLinkTypeAux LocalDef = "def"
getDGLinkTypeAux GlobalDef = "globaldef"
getDGLinkTypeAux HidingDef = "hidingdef"
getDGLinkTypeAux (FreeDef _) = "def"
getDGLinkTypeAux (CofreeDef _) = "def"
getDGLinkTypeAux (LocalThm thmLinkStatus _ _) = 
    "local"++(getThmType thmLinkStatus)++"thm"
getDGLinkTypeAux (GlobalThm thmLinkStatus _ _) = 
    (getThmType thmLinkStatus)++"thm"
getDGLinkTypeAux (HidingThm _ thmLinkStatus) =
    (getThmType thmLinkStatus)++"hidingthm"
getDGLinkTypeAux (FreeThm _ bool) = if bool then "proventhm" else "unproventhm"

getThmType :: ThmLinkStatus -> String
getThmType thmLinkStatus =
  case thmLinkStatus of
    Proven _ -> "proven"
    Open -> "unproven"

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
        Result newDescr err <- addlink descr (getDGLinkType edgelab)
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
      _ -> error "Cannot find nodes"


showReferencedLibrary :: IORef GraphMem -> Descr -> Descr -> GraphInfo 
	      -> ConversionMaps -> HetcatsOpts -> IO (Descr, GraphInfo, ConversionMaps)
showReferencedLibrary graphMem descr abstractGraph graphInfo convMaps hetsOpts =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,node) -> 
         case Map.lookup libname libname2dgMap of
	  Just (_,_,dgraph) -> 
            do let (_,(DGRef _ refLibname refNode)) = 
		       labNode' (context node dgraph)
	       case Map.lookup refLibname libname2dgMap of
                 Just (_,refDgraph,_) -> 
		     convertGraph graphMem refLibname (libname2dg convMaps) hetsOpts
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
					       (head visibleNodes) parentNode))
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


getNodesOfSubtree :: DGraph -> [Node] -> Node -> [Node]
getNodesOfSubtree dgraph visibleNodes node = 
    (concat (map (getNodesOfSubtree dgraph remainingVisibleNodes) predOfNode))
    ++predOfNode
    where predOfNode = --filter (elemR (head visibleNodes)) (pre dgraph node)
           [n| n <- (pre dgraph node), elem n visibleNodes]
          remainingVisibleNodes = [n| n <- visibleNodes, notElem n predOfNode]

elemR :: Eq a => [a] -> a -> Bool
elemR list element = elem element list

notElemR :: Eq a => [a] -> a -> Bool
notElemR list element = notElem element list



-- -- ################ einbindung von proofs.hs ############
applyChanges :: Descr -> LIB_NAME -> GraphInfo -> Descr -> IORef [[Node]]
	          -> ConversionMaps
	          -> [([DGRule],[DGChange])]
		  -> IO (Descr, ConversionMaps)
applyChanges gid libname graphInfo eventDescr ioRefVisibleNodes
	     convMaps history =
  case history of
    [] -> return (eventDescr, convMaps)
    (historyElem:list) ->
      case snd historyElem of
	[] -> return (eventDescr, convMaps)
	changes@(x:xs) -> do
          visibleNodes <- readIORef ioRefVisibleNodes
          (newVisibleNodes, newEventDescr, newConvMaps) <- 
              applyChangesAux gid libname graphInfo visibleNodes
			  eventDescr convMaps changes
	  writeIORef ioRefVisibleNodes newVisibleNodes
	  return (newEventDescr, newConvMaps)

applyChangesAux :: Descr -> LIB_NAME -> GraphInfo -> [[Node]] -> Descr
		  -> ConversionMaps -> [DGChange]
	          -> IO ([[Node]], Descr, ConversionMaps)
applyChangesAux _ _ _ visibleNodes eventDescr convMaps [] =
    return (visibleNodes, eventDescr+1, convMaps)
applyChangesAux gid libname graphInfo visibleNodes eventDescr
		convMaps (change:changes) =
  case change of
    InsertNode lnode@(node,nodelab) -> do
      nodetype <- getDGNodeType nodelab
      let nodename = getDGNodeName nodelab
      (Result descr err) <-
	  addnode gid nodetype nodename graphInfo
      case err of
	Nothing ->
	  do let dgNode = (libname,node)
                 newVisibleNodes = map (insertElem node) visibleNodes
		 newConvMaps = 
		     convMaps {dg2abstrNode = 
			       Map.insert dgNode descr (dg2abstrNode convMaps),
			       abstr2dgNode =
			       Map.insert descr dgNode (abstr2dgNode convMaps)}
	     applyChangesAux gid libname graphInfo newVisibleNodes (descr+1) 
			     newConvMaps changes
	Just msg ->
	       error ("applyChangesAux: could not add node " ++ (show node)
		      ++" with name " ++ (show (nodename)) ++ "\n"
		      ++ msg)
    DeleteNode lnode@(node,nodelab) -> do
      let nodename = getDGNodeName nodelab
	  dgnode = (libname,node)
      case Map.lookup dgnode (dg2abstrNode convMaps) of
        Just abstrNode -> do
	  (Result descr err) <- delnode gid abstrNode graphInfo
	  case err of
	    Nothing -> do
                let newVisibleNodes = map (removeElem node) visibleNodes
		    newConvMaps =
		        convMaps {dg2abstrNode =
				  Map.delete dgnode (dg2abstrNode convMaps),
				  abstr2dgNode =
				  Map.delete abstrNode (abstr2dgNode convMaps)}
	        applyChangesAux gid libname graphInfo newVisibleNodes (descr+1)
			        newConvMaps changes
	    Just msg -> error ("applyChangesAux: could not delete node "
			       ++ (show node) ++ " with name " 
			       ++ (show nodename) ++ "\n"
			       ++ msg)
	Nothing -> error ("applyChangesAux: could not delte node " 
			  ++ (show node) ++ " with name " 
			  ++ (show nodename) ++": " ++
			  "node does not exist in abstraction graph")
    InsertEdge ledge@(src,tgt,edgelab) -> 
      do let dg2abstrNodeMap = dg2abstrNode convMaps
         case (Map.lookup (libname,src) dg2abstrNodeMap,
	       Map.lookup (libname,tgt) dg2abstrNodeMap) of
           (Just abstrSrc, Just abstrTgt) ->
             do let dgEdge = (libname, (src,tgt,show edgelab))
	        (Result descr err) <- 
                   addlink gid (getDGLinkType edgelab)
			      "" (Just ledge) abstrSrc abstrTgt graphInfo
	        case err of
	          Nothing ->
	            do let newConvMaps = convMaps 
                              {dg2abstrEdge =
		               Map.insert dgEdge descr (dg2abstrEdge convMaps),
	                       abstr2dgEdge =
		               Map.insert descr dgEdge (abstr2dgEdge convMaps)}
                       applyChangesAux gid libname graphInfo visibleNodes
				 (descr+1) newConvMaps changes
	          Just msg -> 
                   error ("applyChangesAux: could not add link from "
			  ++ (show src) ++ " to " ++ (show tgt) ++ ":\n"
			  ++ (show msg))
           _ -> 
	       error ("applyChangesAux: could not add link " ++ (show src) 
		      ++ " to " ++ (show tgt) ++ ": illigal end nodes")
   

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
 		        applyChangesAux gid libname graphInfo visibleNodes
				 (descr+1) newConvMaps changes
 		   Just msg -> error ("applyChangesAux: could not delete edge "
			              ++ (show abstrEdge) ++ ":\n"
				      ++msg)

	    Nothing -> error ("applyChangesAux: deleted edge from " 
			      ++ (show src) ++ " to " ++ (show tgt) 
			      ++ " of type " ++ (show (dgl_type edgelab))
			      ++ " and origin " ++ (show (dgl_origin edgelab))
			      ++ " of development "
                         ++ "graph does not exist in abstraction graph")


removeElem :: Eq a => a -> [a] -> [a]
removeElem element list = [e | e <- list, e /= element]

insertElem :: a -> [a] -> [a]
insertElem element list = element:list