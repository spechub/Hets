{- |
Module      :  $Header$
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Conversion of development graphs from Logic.DevGraph
   to abstract graphs of the graph display interface
-}

{-
   todo:
   share strings to avoid typos
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
import Logic.Coerce
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover

import Comorphisms.LogicGraph

import Syntax.AS_Library
import Static.DevGraph
import Static.DGToSpec
import Static.AnalysisLibrary

import Proofs.InferBasic
import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift
import Proofs.StatusUtils

import GUI.AbstractGraphView
import GUI.ShowLogicGraph
import GUI.Utils
import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)

import FileDialog
import System.Directory
import Broadcaster(newSimpleBroadcaster,applySimpleUpdate)
import Sources(toSimpleSource)
import DaVinciGraph
import GraphDisp
import GraphConfigure
import TextDisplay
import qualified HTk
import InfoBus

import qualified Common.Lib.Map as Map
import qualified Common.OrderedMap as OMap
import Common.Lib.Pretty as Pretty hiding (isEmpty)
import Common.Id
import Common.PrettyPrint
import qualified Common.Result as Res

import Driver.Options
import Driver.WriteFn
import Driver.ReadFn

import Data.Graph.Inductive.Graph as Graph
import Data.IORef
import Data.Maybe
import List(nub)
import Control.Monad

{- Maps used to track which node resp edge of the abstract graph
correspondes with which of the development graph and vice versa and
one Map to store which libname belongs to which development graph-}

data ConversionMaps = ConversionMaps {
                        dg2abstrNode :: DGraphToAGraphNode,
                        dg2abstrEdge :: DGraphToAGraphEdge,
                        abstr2dgNode :: AGraphToDGraphNode,
                        abstr2dgEdge :: AGraphToDGraphEdge,
                        libname2dg :: LibEnv}

instance PrettyPrint String where -- overlapping !
    printText0 _ c = text (take 25 c)

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

-- | converts the development graph given by its libname into an abstract
-- graph and returns the descriptor of the latter, the graphInfo it is
-- contained in and the conversion maps (see above)
convertGraph :: IORef GraphMem -> LIB_NAME -> LibEnv -> HetcatsOpts
             -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph graphMem libname libEnv opts =
  do let convMaps = ConversionMaps
           {dg2abstrNode = Map.empty::DGraphToAGraphNode,
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,
            libname2dg = libEnv}

     case Map.lookup libname libEnv of
       Just gctx ->
        do let dgraph = devGraph gctx
           (abstractGraph,grInfo,convRef) <-
                  initializeGraph graphMem libname dgraph convMaps
                                  gctx opts
           if (isEmpty dgraph) then
                return (abstractGraph, grInfo,convMaps)
            else
             do newConvMaps <- convertNodes convMaps abstractGraph
                               grInfo dgraph libname
                finalConvMaps <- convertEdges newConvMaps abstractGraph
                                grInfo dgraph libname
                writeIORef convRef finalConvMaps
                return (abstractGraph, grInfo, finalConvMaps)

       Nothing -> error ("development graph with libname "
                          ++ (show libname)
                           ++ " does not exist")

-- | initializes an empty abstract graph with the needed node and edge types,
-- return type equals the one of convertGraph
initializeGraph :: IORef GraphMem -> LIB_NAME -> DGraph -> ConversionMaps
                     -> GlobalContext -> HetcatsOpts
                     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ioRefGraphMem ln dGraph convMaps _ opts = do
  graphMem <- readIORef ioRefGraphMem
  event <- newIORef 0
  convRef <- newIORef convMaps
  showInternalNames <- newIORef (InternalNames False [])
  ioRefProofStatus <- newIORef $ libname2dg convMaps
  ioRefSubtreeEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  ioRefVisibleNodes <- newIORef [(Graph.nodes dGraph)]
  let gid = nextGraphId graphMem
      actGraphInfo = graphInfo graphMem
  let gInfo = (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo
              , showInternalNames, opts, ioRefVisibleNodes)
  Result descr msg <-
    makegraph ("Development graph for "++show ln)
         -- action on "open"
             (do currentPath <- getCurrentDirectory
                 evnt <- fileDialogStr "Open..." currentPath
                 maybeFilePath <- HTk.sync evnt
                 case maybeFilePath of
                   Just filePath ->
                           do openProofStatus ln filePath ioRefProofStatus
                                              convRef opts
                              return ()
                   Nothing -> fail "Could not open file."
              )
         -- action on "save"
             (encapsulateWaitTermAct
               (do proofStatus <- readIORef ioRefProofStatus
                   let filename = libNameToFile opts ln ++ prfSuffix
                   writeShATermFile filename (ln, lookupHistory ln proofStatus)
                   putStrLn ("Wrote "++filename)))
         -- action on "save as...:"
             (encapsulateWaitTermAct
               (do currentPath <- getCurrentDirectory
                   evnt <- newFileDialogStr "Save as..." currentPath
                   maybeFilePath <- HTk.sync evnt
                   case maybeFilePath of
                     Just filePath -> do
                       proofStatus <- readIORef ioRefProofStatus
                       writeShATermFile filePath $ lookupHistory ln proofStatus
                       putStrLn ("Wrote "++filePath)
                     Nothing -> fail "Could not save file."
               ))
         -- the global menu
             [GlobalMenu (Menu Nothing
               [Menu (Just "Unnamed nodes")
                 [Button "Hide/show names"
                    (do (intrn::InternalNames) <- readIORef showInternalNames
                        let showThem = not $ showNames intrn
                            showItrn s = if showThem then s else ""
                        mapM_ (\(s,upd) -> upd (\_ -> showItrn s))
                              $ updater intrn
                        writeIORef showInternalNames
                                   $ intrn {showNames = showThem}
                        redisplay gid actGraphInfo
                        return ()      ),
                  Button "Hide nodes"
                          (do Result descr msg
                                <- hideSetOfNodeTypes gid
                                       ["open_cons__internal",
                                        "locallyEmpty__open_cons__internal",
                                        "proven_cons__internal",
                                        "locallyEmpty__proven_cons__internal"]
                                                    actGraphInfo
                              writeIORef event descr
                              case msg of
                                Nothing -> do redisplay gid actGraphInfo
                                              return ()
                                Just err -> putStrLn err
                              return () ),
                   Button "Show nodes"
                          (do descr <- readIORef event
                              showIt gid descr actGraphInfo
                              redisplay gid actGraphInfo
                              return ()    )],

                Menu (Just "Proofs")
                  [Button "Automatic"
                          (proofMenu gInfo (return . return . automatic ln)),
                   Button "Global Subsumption"
                          (proofMenu gInfo (return . return . globSubsume ln)),
                   Button "Global Decomposition"
                          (proofMenu gInfo (return . return . globDecomp ln)),
                   Button "Local Inference"
                          (proofMenu gInfo (return . return .
                                            localInference ln)),
                   Button "Local Decomposition (merge of rules)"
                          (proofMenu gInfo (return . return . locDecomp ln)),
                   Button "Composition (merge of rules)"
                          (proofMenu gInfo (return . return . composition ln)),
                   Button "Composition - creating new links"
                          (proofMenu gInfo (return . return .
                                            compositionCreatingEdges ln)),
                   Button "Hide Theorem Shift"
                          (proofMenu gInfo (fmap return .
                                            interactiveHideTheoremShift ln)),
                   Button "Theorem Hide Shift"
                          (proofMenu gInfo (return . return .
                                                   theoremHideShift ln))
                    ]])]
      -- the node types
               [("open_cons__spec",
                 createLocalMenuNodeTypeSpec "Coral" ioRefSubtreeEvents
                                  actGraphInfo ioRefGraphMem gInfo
                ),
                ("proven_cons__spec",
                 createLocalMenuNodeTypeSpec "Coral" ioRefSubtreeEvents
                                  actGraphInfo ioRefGraphMem gInfo
                ),
                ("locallyEmpty__open_cons__spec",
                 createLocalMenuNodeTypeSpec "Coral" ioRefSubtreeEvents
                                  actGraphInfo ioRefGraphMem gInfo
                ),
                ("locallyEmpty__proven_cons__spec",
                 createLocalMenuNodeTypeSpec "Green" ioRefSubtreeEvents
                                  actGraphInfo ioRefGraphMem gInfo
                ),
                ("open_cons__internal",
                 createLocalMenuNodeTypeInternal "Coral" gInfo
                ),
                ("proven_cons__internal",
                 createLocalMenuNodeTypeInternal "Coral" gInfo
                ),
                ("locallyEmpty__open_cons__internal",
                 createLocalMenuNodeTypeInternal "Coral" gInfo
                ),
                ("locallyEmpty__proven_cons__internal",
                 createLocalMenuNodeTypeInternal "Green" gInfo
                ),
                ("dg_ref",
                 createLocalMenuNodeTypeDgRef "Coral" actGraphInfo
                                              ioRefGraphMem graphMem gInfo
                 ),
                ("locallyEmpty__dg_ref",
                 createLocalMenuNodeTypeDgRef "Green"
                        actGraphInfo ioRefGraphMem graphMem gInfo
                 ) ]
      -- the link types (share strings to avoid typos)
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
                   Solid $$$ Color "Coral"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localproventhm",
                   Dashed $$$ Color "Green"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("localunproventhm",
                   Dashed $$$ Color "Coral"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("unprovenhidingthm",
                   Solid $$$ Color "Yellow"
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
                  ("globaldef","hidingdef","hidingdef"),
                  ("globaldef","hetdef","hetdef"),
                  ("globaldef","proventhm","proventhm"),
                  ("globaldef","unproventhm","unproventhm"),
                  ("globaldef","localunproventhm","localunproventhm"),
                  ("def","globaldef","def"),
                  ("def","def","def"),
                  ("def","hidingdef","hidingdef"),
                  ("def","hetdef","hetdef"),
                  ("def","proventhm","proventhm"),
                  ("def","unproventhm","unproventhm"),
                  ("def","localunproventhm","localunproventhm"),
                  ("hidingdef","globaldef","hidingdef"),
                  ("hidingdef","def","def"),
                  ("hidingdef","hidingdef","hidingdef"),
                  ("hidingdef","hetdef","hetdef"),
                  ("hidingdef","proventhm","proventhm"),
                  ("hidingdef","unproventhm","unproventhm"),
                  ("hidingdef","localunproventhm","localunproventhm"),
                  ("hetdef","globaldef","hetdef"),
                  ("hetdef","def","hetdef"),
                  ("hetdef","hidingdef","hetdef"),
                  ("hetdef","hetdef","hetdef"),
                  ("hetdef","proventhm","proventhm"),
                  ("hetdef","unproventhm","unproventhm"),
                  ("hetdef","localunproventhm","localunproventhm"),
                  ("proventhm","globaldef","proventhm"),
                  ("proventhm","def","proventhm"),
                  ("proventhm","hidingdef","proventhm"),
                  ("proventhm","hetdef","proventhm"),
                  ("proventhm","proventhm","proventhm"),
                  ("proventhm","unproventhm","unproventhm"),
                  ("proventhm","localunproventhm","localunproventhm"),
                  ("unproventhm","globaldef","unproventhm"),
                  ("unproventhm","def","unproventhm"),
                  ("unproventhm","hidingdef","unproventhm"),
                  ("unproventhm","hetdef","unproventhm"),
                  ("unproventhm","proventhm","unproventhm"),
                  ("unproventhm","unproventhm","unproventhm"),
                  ("unproventhm","localunproventhm","localunproventhm"),
                  ("localunproventhm","globaldef","localunproventhm"),
                  ("localunproventhm","def","localunproventhm"),
                  ("localunproventhm","hidingdef","localunproventhm"),
                  ("localunproventhm","hetdef","localunproventhm"),
                  ("localunproventhm","proventhm","localunproventhm"),
                  ("localunproventhm","unproventhm","localunproventhm"),
                  ("localunproventhm","localunproventhm","localunproventhm")]
                 actGraphInfo
  case msg of
    Nothing -> return ()
    Just err -> fail err
  writeIORef ioRefGraphMem graphMem{nextGraphId = gid+1}
  graphMem'<- readIORef ioRefGraphMem
  return (descr,graphInfo graphMem',convRef)

-- | implementation of open menu, read in a proof status
openProofStatus :: LIB_NAME -> FilePath -> (IORef ProofStatus)
                -> (IORef ConversionMaps)
                -> HetcatsOpts -> IO(Descr, GraphInfo, ConversionMaps)
openProofStatus libname file ioRefProofStatus convRef opts =
  if fileToLibName opts file /= libname then
      error $ "file name must correspond to library name: "
                ++ showPretty libname ""
  else
  do m <- anaLib opts file
     case m of
       Nothing -> error $ "Could not read proof status from file '"
                  ++ file ++ "'"
       Just (ln, libEnv) -> do
            proofStatus <- readPrfFiles opts libEnv
            writeIORef ioRefProofStatus proofStatus
            initGraphInfo <- initgraphs
            graphMem' <- (newIORef GraphMem{nextGraphId = 0,
                                      graphInfo = initGraphInfo})
            let ln = fileToLibName opts file
            (gid, actGraphInfo, convMaps)
                          <- convertGraph graphMem' ln proofStatus opts
            writeIORef convRef convMaps
            redisplay gid actGraphInfo
            return (gid, actGraphInfo, convMaps)

-- | apply a rule of the development graph calculus
proofMenu :: GInfo
             -> (ProofStatus -> IO (Res.Result ProofStatus))
             -> IO ()
proofMenu (ioRefProofStatus, event, convRef, gid, ln, actGraphInfo, _
          , hOpts, ioRefVisibleNodes) proofFun = do
  proofStatus <- readIORef ioRefProofStatus
  putIfVerbose hOpts 4 "Proof started via \"Proofs\" menu"
  Res.Result diags res <- proofFun proofStatus
  putIfVerbose hOpts 4 "Analyzing result of proof"
  case res of
    Nothing -> mapM_ (putStrLn . show) diags
    Just newProofStatus -> do
      let newGlobContext = lookupGlobalContext ln newProofStatus
          history = proofHistory newGlobContext
      writeIORef ioRefProofStatus newProofStatus
      descr <- readIORef event
      convMaps <- readIORef convRef
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

proofMenuSef :: GInfo -> (ProofStatus -> ProofStatus) -> IO ()
proofMenuSef gInfo proofFun = proofMenu gInfo (return . return . proofFun)

-- -------------------------------------------------------------
-- methods to create the local menus of the different nodetypes
-- -------------------------------------------------------------

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec color ioRefSubtreeEvents actGraphInfo
             ioRefGraphMem gInfo@(_,_,convRef,_,_,_,_,_,ioRefVisibleNodes) =
                 Ellipse $$$ Color color
                 $$$ ValueTitle (\ (s,_,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSpec gInfo,
                    createLocalMenuButtonShowNumberOfNode,
                    createLocalMenuButtonShowSignature gInfo,
                    createLocalMenuButtonShowLocalAx gInfo,
                    createLocalMenuButtonShowTheory gInfo,
                    createLocalMenuButtonTranslateTheory gInfo,
                    createLocalMenuTaxonomy gInfo,
                    createLocalMenuButtonShowSublogic gInfo,
                    createLocalMenuButtonShowNodeOrigin gInfo,
                    createLocalMenuButtonShowProofStatusOfNode gInfo,
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


-- | local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal color
                          gInfo@(_,_,_,_,_,_,showInternalNames,_,_) =
                 Ellipse $$$ Color color
                 $$$ ValueTitleSource (\ (s,_,_) -> do
                       b <- newSimpleBroadcaster ""
                       intrn <- readIORef showInternalNames
                       let upd = (s,applySimpleUpdate b)
                       writeIORef showInternalNames
                                      $ intrn {updater = upd:updater intrn}
                       return $ toSimpleSource b)
                 $$$ LocalMenu (Menu (Just "node menu")
                    [createLocalMenuButtonShowSpec gInfo,
                     createLocalMenuButtonShowNumberOfNode,
                     createLocalMenuButtonShowSignature gInfo,
                    createLocalMenuButtonShowLocalAx gInfo,
                     createLocalMenuButtonShowTheory gInfo,
                     createLocalMenuButtonTranslateTheory gInfo,
                     createLocalMenuTaxonomy gInfo,
                     createLocalMenuButtonShowSublogic gInfo,
                     createLocalMenuButtonShowProofStatusOfNode gInfo,
                     createLocalMenuButtonProveAtNode gInfo,
                     createLocalMenuButtonCCCAtNode gInfo,
                     createLocalMenuButtonShowNodeOrigin gInfo])
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)

-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef color actGraphInfo
                             ioRefGraphMem graphMem
                             gInfo@(_,_,convRef,_,_,_,_,opts,_) =
                 Box $$$ Color color
                 $$$ ValueTitle (\ (s,_,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSignature gInfo,
                    createLocalMenuButtonShowTheory gInfo,
                    createLocalMenuButtonProveAtNode gInfo,
                    createLocalMenuButtonShowProofStatusOfNode gInfo,
                    Button "Show referenced library"
                     (\ (_, descr, gid) ->
                        do convMaps <- readIORef convRef
                           (refDescr, newGraphInfo, _) <-
                                showReferencedLibrary ioRefGraphMem descr
                                              gid
                                              actGraphInfo
                                              convMaps
                                              opts
--writeIORef convRef newConvMaps
                           writeIORef ioRefGraphMem
                                      graphMem{graphInfo = newGraphInfo,
                                               nextGraphId = refDescr +1}
                           redisplay refDescr newGraphInfo
                           return ()
                     )])
                 $$$ emptyNodeTypeParms
                     :: DaVinciNodeTypeParms (String,Int,Int)


-- | menu button for local menus
createMenuButton title menuFun (ioProofStatus,_,convRef,_,ln,_,_,_,_) =
                    (Button title
                      (\ (_, descr, _) ->
                        do convMaps <- readIORef convRef
                           ps <- readIORef ioProofStatus
                           let dGraph = lookupDGraph ln ps
                           menuFun descr
                                   (abstr2dgNode convMaps)
                                   dGraph
                           return ()
                       )
                    )


createLocalMenuButtonShowSpec = createMenuButton "Show spec" showSpec
createLocalMenuButtonShowSignature =
  createMenuButton "Show signature" getSignatureOfNode
createLocalMenuButtonShowTheory gInfo =
  createMenuButton "Show theory" (getTheoryOfNode gInfo) gInfo
createLocalMenuButtonShowLocalAx gInfo =
  createMenuButton "Show local axioms" (getLocalAxOfNode gInfo) gInfo
createLocalMenuButtonTranslateTheory gInfo =
  createMenuButton "Translate theory" (translateTheoryOfNode gInfo) gInfo


{- |
   create a sub Menu for taxonomy visualisation
   (added by KL)
-}
createLocalMenuTaxonomy ginfo@(proofStatus,_,_,_,_,_,_,_,_) =
      (Menu (Just "Taxonomy graphs")
       [createMenuButton "Subsort graph"
               (passTh displaySubsortGraph) ginfo,
        createMenuButton "Concept graph"
               (passTh displayConceptGraph) ginfo])
    where passTh displayFun descr ab2dgNode dgraph =
              do r <- lookupTheoryOfNode proofStatus
                                         descr ab2dgNode dgraph
                 case r of
                  Res.Result [] (Just (n, gth)) ->
                      displayFun (showPretty n "") gth
                  Res.Result diags _ ->
                     showDiags defaultHetcatsOpts diags



createLocalMenuButtonShowSublogic gInfo@(proofStatus,_,_,_,_,_,_,_,_) =
  createMenuButton "Show sublogic" (getSublogicOfNode proofStatus) gInfo
createLocalMenuButtonShowNodeOrigin  =
  createMenuButton "Show origin" showOriginOfNode
createLocalMenuButtonShowProofStatusOfNode gInfo =
  createMenuButton "Show proof status" (showProofStatusOfNode gInfo) gInfo
createLocalMenuButtonProveAtNode gInfo =
  createMenuButton "Prove" (proveAtNode False gInfo) gInfo
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (proveAtNode True gInfo) gInfo


createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents convRef
    ioRefVisibleNodes ioRefGraphMem actGraphInfo =
                    (Button "Show just subtree"
                      (\ (_, descr, gid) ->
                        do subtreeEvents <- readIORef ioRefSubtreeEvents
                           case Map.lookup descr subtreeEvents of
                             Just _ -> putStrLn $
                               "it is already just the subtree of node "
                                ++  show descr ++" shown"
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
                                    Just stext -> putStrLn stext
                      )
                    )


createLocalMenuButtonUndoShowJustSubtree ioRefVisibleNodes
                                         ioRefSubtreeEvents actGraphInfo =
                    (Button "Undo show just subtree"
                      (\ (_, descr, gid) ->
                        do visibleNodes <- readIORef ioRefVisibleNodes
                           case (tail visibleNodes) of
                             [] -> do putStrLn
                                          "Complete graph is already shown"
                                      return()
                             newVisibleNodes@(_ : _) ->
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

-- | for debugging
createLocalMenuButtonShowNumberOfNode =
  (Button "Show number of node"
    (\ (_, descr, _) ->
       getNumberOfNode descr))

-- -------------------------------------------------------------
-- methods to create the local menus for the edges
-- -------------------------------------------------------------
createLocalEdgeMenu gInfo =
    LocalMenu (Menu (Just "edge menu")
               [createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo]
              )

createLocalEdgeMenuThmEdge gInfo =
   LocalMenu (Menu (Just "thm egde menu")
              [createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonShowProofStatusOfThm gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo]
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

createLocalMenuButtonCheckconservativityOfEdge gInfo =
  (Button "Check conservativity (preliminary)"
                      (\ (_, descr, maybeLEdge)  ->
                        do checkconservativityOfEdge descr gInfo maybeLEdge
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
        (_,LeftOpen) -> (show c) ++ "?"
        _ -> show c

-- ------------------------------
-- end of local menu definitions
-- ------------------------------

showSpec descr convMap dgraph =
  case Map.lookup descr convMap of
   Nothing -> return ()
   Just (_, node) -> do
      let sp = dgToSpec dgraph node
      putStrLn (showPretty sp "")

{- | auxiliary method for debugging. shows the number of the given node
     in the abstraction graph -}
getNumberOfNode :: Descr -> IO()
getNumberOfNode descr =
  let title = "Number of node"
    in createTextDisplay title (showPretty descr "") [HTk.size(10,10)]

{- | outputs the signature of a node in a window;
used by the node menu defined in initializeGraph -}
getSignatureOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
getSignatureOfNode descr ab2dgNode dgraph =
  case Map.lookup descr ab2dgNode of
    Just (_, node) ->
      let dgnode = lab' (context dgraph node)
          title = "Signature of "++showName (dgn_name dgnode)
       in createTextDisplay title (showPretty (dgn_sign dgnode) "")
                            [HTk.size(80,50)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

{- |
   fetches the theory from a node inside the IO Monad
   (added by KL based on code in getTheoryOfNode) -}
lookupTheoryOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode ->
                      DGraph -> IO (Res.Result (Node,G_theory))
lookupTheoryOfNode proofStatusRef descr ab2dgNode _ = do
 libEnv <- readIORef proofStatusRef
 case (do
  libNode@(_, node) <-
        Res.maybeToResult nullRange ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode
  gth <- computeTheory libEnv libNode
  return (node, gth)
    ) of
   r -> return r

{- | outputs the local axioms of a node in a window;
used by the node menu defined in initializeGraph-}
getLocalAxOfNode :: GInfo -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
getLocalAxOfNode _ descr ab2dgNode dgraph = do
  case Map.lookup descr ab2dgNode of
    Just (_, node) ->
      do let dgnode = lab' (context dgraph node)
         case dgnode of
           DGNode _ gth _ _ _ _ _ ->
              displayTheory "Local Axioms" node dgraph gth
           DGRef name _ _ _ _ _ ->
              createTextDisplay ("Local Axioms of "++ showName name)
                    "no local axioms (reference node to other library)"
                    [HTk.size(30,10)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

{- | outputs the theory of a node in a window;
used by the node menu defined in initializeGraph-}
getTheoryOfNode :: GInfo -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
getTheoryOfNode (proofStatusRef,_,_,_,_,_,_,opts,_)
                descr ab2dgNode dgraph = do
 r <- lookupTheoryOfNode proofStatusRef descr ab2dgNode dgraph
 case r of
  Res.Result diags res -> do
    showDiags opts diags
    case res of
      (Just (n, gth)) -> displayTheory "Theory" n dgraph gth
      _ -> return ()

displayTheory :: String -> Node -> DGraph -> G_theory
              -> IO ()
displayTheory ext node dgraph gth =
    let dgnode = lab' (context dgraph node)
        str = showPretty gth "\n"
        thname = showName (dgn_name dgnode)
        title = ext ++ " of " ++ thname
     in createTextSaveDisplay title (thname++".het") str


{- | translate the theory of a node in a window;
used by the node menu defined in initializeGraph-}
translateTheoryOfNode :: GInfo -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
translateTheoryOfNode (proofStatusRef,_,_,_,_,_,_,opts,_)
                      descr ab2dgNode dgraph = do
 libEnv <- readIORef proofStatusRef
 case (do
   libNode@(_, node) <-
        Res.maybeToResult nullRange ("Node "++show descr++" not found")
                       $ Map.lookup descr ab2dgNode
   th <- computeTheory libEnv libNode
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
           _ -> Res.resToIORes $ Res.fatal_error "" nullRange
         Comorphism cid <- return (paths!!i)
         -- adjust lid's
         let lidS = sourceLogic cid
             lidT = targetLogic cid
         sign' <- coerceSign lid lidS "" sign
         sens' <- coerceThSens lid lidS "" sens
         -- translate theory along chosen comorphism
         (sign'',sens1) <-
             Res.resToIORes $ map_theory cid (sign', toNamedList sens')
         Res.ioToIORes $ displayTheory "Translated theory" node dgraph
            (G_theory lidT sign'' $ toThSens sens1)
     )
    showDiags opts diags
    return ()
  Res.Result diags _ -> showDiags opts diags

{- | outputs the sublogic of a node in a window;
used by the node menu defined in initializeGraph-}
getSublogicOfNode :: IORef ProofStatus -> Descr -> AGraphToDGraphNode
                  -> DGraph -> IO()
getSublogicOfNode proofStatusRef descr ab2dgNode dgraph = do
  libEnv <- readIORef proofStatusRef
  case Map.lookup descr ab2dgNode of
    Just libNode@(_, node) ->
      let dgnode = lab' (context dgraph node)
          name = case dgnode of
                       (DGNode nname _ _ _ _ _ _) -> nname
                       _ -> emptyNodeName
       in case computeTheory libEnv libNode of
        Res.Result _ (Just th) ->
                let logstr = show $ sublogicOfTh th
                    title =  "Sublogic of "++showName name
                 in createTextDisplay title logstr [HTk.size(30,10)]
        Res.Result diags _ ->
          error ("Could not compute theory for sublogic computation: "++
                concatMap show diags)
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")


{- | prints the origin of the node -}
showOriginOfNode :: Descr -> AGraphToDGraphNode -> DGraph -> IO()
showOriginOfNode descr ab2dgNode dgraph =
  case Map.lookup descr ab2dgNode of
    Just (_, node) ->
      do let dgnode = lab' (context dgraph node)
         case dgnode of
           DGNode name _ _ _ orig _ _ ->
              let title =  "Origin of node "++showName name
               in createTextDisplay title
                    (showPretty orig "") [HTk.size(30,10)]
           DGRef _ _ _ _ _ _ -> error "showOriginOfNode: no DGNode"
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

-- | Show proof status of a node
showProofStatusOfNode _ descr ab2dgNode dgraph =
  case Map.lookup descr ab2dgNode of
    Just (_, node) ->
      do let dgnode = lab' (context dgraph node)
         let stat = showStatusAux dgnode
         let title =  "Proof status of node "++showName (dgn_name dgnode)
         createTextDisplay title stat [HTk.size(105,55)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

showStatusAux :: DGNodeLab -> String
showStatusAux dgnode =
  case dgn_theory dgnode of
  G_theory _ _ sens ->
     let goals = OMap.filter (not . isAxiom) sens
         (proven,open) = OMap.partition isProvenSenStatus goals
      in "Proven proof goals:\n"
         ++ showPretty proven ""
         ++ if not (isRefNode dgnode) && dgn_cons dgnode /= None
                && dgn_cons_status dgnode /= LeftOpen
             then showPretty (dgn_cons_status dgnode)
                      "is the conservativity status of this node"
             else ""
         ++ "\nOpen proof goals:\n"
         ++ showPretty open ""
         ++ if not (isRefNode dgnode) && dgn_cons dgnode /= None
                && dgn_cons_status dgnode == LeftOpen
             then showPretty (dgn_cons_status dgnode)
                      "should be the conservativity status of this node"
             else ""


-- | start local theorem proving or consistency checking at a node
proveAtNode :: Bool -> GInfo -> Descr -> AGraphToDGraphNode -> DGraph -> IO()
proveAtNode checkCons gInfo@(_,_,_,_,ln,_,_,_,_) descr ab2dgNode _ =
  case Map.lookup descr ab2dgNode of
    Just libNode ->
         proofMenu gInfo (basicInferenceNode checkCons logicGraph libNode ln)
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")


-- | print the morphism of the edge
showMorphismOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showMorphismOfEdge _ (Just (_,_,linklab)) =
      createTextDisplay "Signature morphism"
           ((showPretty (dgl_morphism linklab) "")++hidingMorph)
           [HTk.size(150,50)]
  where
    hidingMorph = case (dgl_type linklab) of
                    (HidingThm morph _) -> "\n ++++++ \n"
                                           ++ (showPretty morph "")
                    _ -> ""
showMorphismOfEdge descr Nothing =
      createTextDisplay "Error"
          ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph") [HTk.size(30,10)]


-- | print the origin of the edge
showOriginOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showOriginOfEdge _ (Just (_,_,linklab)) =
      createTextDisplay "Origin of link"
        (showPretty (dgl_origin linklab) "")  [HTk.size(30,10)]
showOriginOfEdge descr Nothing =
      createTextDisplay "Error"
         ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph") [HTk.size(30,10)]

-- | print the proof base of the edge
showProofStatusOfThm :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showProofStatusOfThm _ (Just ledge) =
    createTextSaveDisplay "Proof Status" "proofstatus.txt"
         (showPretty (getProofStatusOfThm ledge) "\n")
showProofStatusOfThm descr Nothing =
    putStrLn ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph")

-- | check conservativity of the edge
checkconservativityOfEdge :: Descr -> GInfo -> Maybe (LEdge DGLinkLab) -> IO()
checkconservativityOfEdge _ (ref,_,_,_,ln,_,_,_,_)
                           (Just (source,target,linklab)) = do
  ps@libEnv <- readIORef ref
  let dgraph = lookupDGraph ln ps
      dgtar = lab' (context dgraph target)
  case dgtar of
    DGNode _ (G_theory lid _ sens) _ _ _ _ _ ->
     case dgl_morphism linklab of
     GMorphism cid _ morphism2 -> do
      morphism2' <- coerceMorphism (targetLogic cid) lid
                   "checkconservativityOfEdge" morphism2
      let th = case computeTheory libEnv (ln, source) of
                Res.Result _ (Just th1) -> th1
                _ -> error "checkconservativityOfEdge: computeTheory"
      G_theory lid1 sign1 sens1 <- return th
      sign2 <- coerceSign lid1 lid "checkconservativityOfEdge.coerceSign" sign1
      sens2 <- coerceThSens lid1 lid "" sens1
      let Res.Result diags res =
                     conservativityCheck lid (sign2, toNamedList sens2)
                                         morphism2' $ toNamedList sens
          showRes = case res of
                   Just(Just True) -> "The link is conservative"
                   Just(Just False) -> "The link is not conservative"
                   _ -> "Could not determine whether link is conservative"
          myDiags = unlines (map show diags)
      createTextDisplay "Result of conservativity check"
                      (showRes ++ "\n" ++ myDiags) [HTk.size(50,50)]
    DGRef _ _ _ _ _ _ -> error "checkconservativityOfEdge: no DGNode"

checkconservativityOfEdge descr _ Nothing =
      createTextDisplay "Error"
          ("edge " ++ show descr ++ " has no corresponding edge "
                ++ "in the development graph") [HTk.size(30,10)]


getProofStatusOfThm :: (LEdge DGLinkLab) -> ThmLinkStatus
getProofStatusOfThm (_,_,label) =
  case (dgl_type label) of
    (LocalThm proofStatus _ _) -> proofStatus
    (GlobalThm proofStatus _ _) -> proofStatus
    (HidingThm _ proofStatus) -> proofStatus -- richtig?
--  (FreeThm GMorphism Bool) - keinen proofStatus?
    _ -> error "the given edge is not a theorem"

{- | converts the nodes of the development graph, if it has any,
and returns the resulting conversion maps
if the graph is empty the conversion maps are returned unchanged-}
convertNodes :: ConversionMaps -> Descr -> GraphInfo -> DGraph
                  -> LIB_NAME -> IO ConversionMaps
convertNodes convMaps descr grInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertNodesAux convMaps
                                descr
                                grInfo
                                (labNodes dgraph)
                                libname


{- | auxiliary function for convertNodes if the given list of nodes is
emtpy, it returns the conversion maps unchanged otherwise it adds the
converted first node to the abstract graph and to the affected
conversion maps and afterwards calls itself with the remaining node
list -}
convertNodesAux :: ConversionMaps -> Descr -> GraphInfo ->
                     [LNode DGNodeLab] -> LIB_NAME -> IO ConversionMaps
convertNodesAux convMaps _ _ [] _ = return convMaps
convertNodesAux convMaps descr grInfo ((node,dgnode) : lNodes) libname =
  do let nodetype = getDGNodeType dgnode
     Result newDescr _ <- addnode descr
                                nodetype
                                (getDGNodeName dgnode)
                                grInfo
     convertNodesAux convMaps {dg2abstrNode = Map.insert (libname, node)
                                       newDescr (dg2abstrNode convMaps),
                                 abstr2dgNode = Map.insert newDescr
                                      (libname, node) (abstr2dgNode convMaps)}
                                       descr grInfo lNodes libname


-- | gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> String
getDGNodeType dgnodelab =
    (if locallyEmpty dgnodelab then "locallyEmpty__"  else "")
    ++ case isDGRef dgnodelab of
       True -> "dg_ref"
       False -> (if hasOpenConsStatus dgnodelab
                 then "open_cons__"
                 else "proven_cons__")
                ++ if isInternalNode dgnodelab
                   then "internal"
                   else "spec"
    where
      hasOpenConsStatus dgn = dgn_cons dgn /= None &&
          case dgn_cons_status dgn of
            LeftOpen -> True
            _ -> False

getDGLinkType :: DGLinkLab -> String
getDGLinkType lnk = case dgl_type lnk of
  GlobalDef ->
    if isHomogeneous $ dgl_morphism lnk then "globaldef"
        else "hetdef"
  HidingDef -> "hidingdef"
  LocalThm thmLnkState _ _ -> "local" ++ getThmType thmLnkState ++ "thm"
  GlobalThm thmLnkState _ _ -> getThmType thmLnkState ++ "thm"
  HidingThm _ thmLnkState -> getThmType thmLnkState ++ "hidingthm"
  FreeThm _ bool -> if bool then "proventhm" else "unproventhm"
  _  -> "def" -- LocalDef, FreeDef, CofreeDef

getThmType :: ThmLinkStatus -> String
getThmType thmLnkState =
  case thmLnkState of
    Proven _ _ -> "proven"
    LeftOpen -> "unproven"

{- | converts the edges of the development graph
works the same way as convertNods does-}
convertEdges :: ConversionMaps -> Descr -> GraphInfo -> DGraph
                  -> LIB_NAME -> IO ConversionMaps
convertEdges convMaps descr grInfo dgraph libname
  | isEmpty dgraph = do return convMaps
  | otherwise = convertEdgesAux convMaps
                                descr
                                grInfo
                                (labEdges dgraph)
                                libname

-- | auxiliary function for convertEges
convertEdgesAux :: ConversionMaps -> Descr -> GraphInfo ->
                    [LEdge DGLinkLab] -> LIB_NAME -> IO ConversionMaps
convertEdgesAux convMaps _ _ [] _ = return convMaps
convertEdgesAux convMaps descr grInfo (ledge@(src,tar,edgelab) : lEdges)
                libname =
  do let srcnode = Map.lookup (libname,src) (dg2abstrNode convMaps)
         tarnode = Map.lookup (libname,tar) (dg2abstrNode convMaps)
     case (srcnode,tarnode) of
      (Just s, Just t) -> do
        Result newDescr msg <- addlink descr (getDGLinkType edgelab)
                                   "" (Just ledge) s t grInfo
        case msg of
          Nothing -> return ()
          Just err -> fail err
        newConvMaps <- (convertEdgesAux
                       convMaps {dg2abstrEdge = Map.insert
                                     (libname, (src,tar,showPretty edgelab ""))
                                     newDescr
                                     (dg2abstrEdge convMaps),
                                 abstr2dgEdge = Map.insert newDescr
                                     (libname, (src,tar,showPretty edgelab ""))
                                     (abstr2dgEdge convMaps)}
                                         descr grInfo lEdges libname)
        return newConvMaps
      _ -> error "Cannot find nodes"

-- | show library referened by a DGRef node (=node drawn as a box)
showReferencedLibrary :: IORef GraphMem -> Descr -> Descr -> GraphInfo
                      -> ConversionMaps -> HetcatsOpts
                      -> IO (Descr, GraphInfo, ConversionMaps)
showReferencedLibrary graphMem descr _ _ convMaps opts =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,node) ->
         case Map.lookup libname libname2dgMap of
          Just gctx ->
            do let dgraph = devGraph gctx
                   (_,(DGRef _ refLibname _ _ _ _)) =
                       labNode' (context dgraph node)
               case Map.lookup refLibname libname2dgMap of
                 Just _ ->
                     convertGraph graphMem refLibname (libname2dg convMaps)
                                  opts
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

-- | prune displayed graph to subtree of selected node
showJustSubtree :: IORef GraphMem -> Descr -> Descr -> ConversionMaps
                -> [[Node]]-> IO (Descr, [[Node]], Maybe String)
showJustSubtree ioRefGraphMem descr abstractGraph convMaps visibleNodes =
  case Map.lookup descr (abstr2dgNode convMaps) of
    Just (libname,parentNode) ->
      case Map.lookup libname libname2dgMap of
        Just gctx  ->
          do let dgraph = devGraph gctx
                 allNodes = getNodeDescriptors (head visibleNodes)
                                            libname convMaps
                 dgNodesOfSubtree = nub (parentNode:(getNodesOfSubtree dgraph
                                               (head visibleNodes) parentNode))
                 -- the selected node (parentNode) shall not be hidden either,
                 -- and we already know its descriptor (descr)
                 nodesOfSubtree = getNodeDescriptors dgNodesOfSubtree
                                  libname convMaps
                 nodesToHide = filter (`notElem` nodesOfSubtree) allNodes
             graphMem <- readIORef ioRefGraphMem
             (Result eventDescr errorMsg) <- hidenodes abstractGraph
                                             nodesToHide (graphInfo graphMem)
             return (eventDescr, (dgNodesOfSubtree:visibleNodes), errorMsg)
{-           case errorMsg of
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
    where predOfNode =
           [n| n <- (pre dgraph node), elem n visibleNodes]
          remainingVisibleNodes = [n| n <- visibleNodes, notElem n predOfNode]

-- | apply the changes history to the displayed development graph
applyHistory :: Descr -> LIB_NAME -> GraphInfo -> Descr -> IORef [[Node]]
                  -> ConversionMaps
                  -> [([DGRule],[DGChange])]
                  -> IO (Descr, ConversionMaps)
applyHistory gid libname grInfo eventDescr ioRefVisibleNodes
             convMaps history =
  applyChangesAux gid libname grInfo ioRefVisibleNodes
        (eventDescr, convMaps) changes
  where changes = removeContraryChanges (concatMap snd history)


-- | apply the changes of first history item (computed by proof rules,
-- see folder Proofs) to the displayed development graph
applyChanges :: Descr -> LIB_NAME -> GraphInfo -> Descr -> IORef [[Node]]
                  -> ConversionMaps
                  -> [([DGRule],[DGChange])]
                  -> IO (Descr, ConversionMaps)
applyChanges _ _ _ eventDescr _ convMaps [] = return (eventDescr,convMaps)
applyChanges gid libname grInfo eventDescr ioRefVisibleNodes
             convMaps (historyElem:_) =
  applyChangesAux gid libname grInfo ioRefVisibleNodes
        (eventDescr, convMaps) changes
  where changes = removeContraryChanges (snd historyElem)

-- | auxiliary function for applyChanges
applyChangesAux :: Descr -> LIB_NAME -> GraphInfo -> IORef [[Node]]
                  -> (Descr, ConversionMaps)
                  -> [DGChange]
                  -> IO (Descr, ConversionMaps)
applyChangesAux gid libname grInfo  ioRefVisibleNodes
            (eventDescr, convMaps) changeList  =
  case changeList of
    [] -> return (eventDescr, convMaps)
    changes@(_:_) -> do
      --putStrLn ("applyChangesAux:\n"++show changes)
      visibleNodes <- readIORef ioRefVisibleNodes
      (newVisibleNodes, newEventDescr, newConvMaps) <-
          applyChangesAux2 gid libname grInfo visibleNodes
                      eventDescr convMaps changes
      writeIORef ioRefVisibleNodes newVisibleNodes
      return (newEventDescr, newConvMaps)

-- | auxiliary function for applyChanges
applyChangesAux2 :: Descr -> LIB_NAME -> GraphInfo -> [[Node]] -> Descr
                  -> ConversionMaps -> [DGChange]
                  -> IO ([[Node]], Descr, ConversionMaps)
applyChangesAux2 _ _ _ visibleNodes eventDescr convMaps [] =
    return (visibleNodes, eventDescr+1, convMaps)
applyChangesAux2 gid libname grInfo visibleNodes _ convMaps (change:changes) =
  case change of
    InsertNode (node, nodelab) -> do
      let nodetype = getDGNodeType nodelab
          nodename = getDGNodeName nodelab
      -- putStrLn ("inserting node "++show nodename++" of type "++show nodetype)
      (Result descr err) <-
          addnode gid nodetype nodename grInfo
      case err of
        Nothing ->
          do let dgNode = (libname,node)
                 newVisibleNodes = map (node :) visibleNodes
                 newConvMaps =
                     convMaps {dg2abstrNode =
                               Map.insert dgNode descr (dg2abstrNode convMaps),
                               abstr2dgNode =
                               Map.insert descr dgNode (abstr2dgNode convMaps)}
             applyChangesAux2 gid libname grInfo newVisibleNodes (descr+1)
                             newConvMaps changes
        Just msg ->
               error ("applyChangesAux2: could not add node " ++ (show node)
                      ++" with name " ++ (show (nodename)) ++ "\n"
                      ++ msg)
    DeleteNode (node, nodelab) -> do
      let nodename = getDGNodeName nodelab
          dgnode = (libname,node)
      -- putStrLn ("inserting node "++show nodename)
      case Map.lookup dgnode (dg2abstrNode convMaps) of
        Just abstrNode -> do
          (Result descr err) <- delnode gid abstrNode grInfo
          case err of
            Nothing -> do
                let newVisibleNodes = map (filter (/= node)) visibleNodes
                    newConvMaps =
                        convMaps {dg2abstrNode =
                                  Map.delete dgnode (dg2abstrNode convMaps),
                                  abstr2dgNode =
                                  Map.delete abstrNode (abstr2dgNode convMaps)}
                applyChangesAux2 gid libname grInfo newVisibleNodes (descr+1)
                                newConvMaps changes
            Just msg -> error ("applyChangesAux2: could not delete node "
                               ++ (show node) ++ " with name "
                               ++ (show nodename) ++ "\n"
                               ++ msg)
        Nothing -> error ("applyChangesAux2: could not delte node "
                          ++ (show node) ++ " with name "
                          ++ (show nodename) ++": " ++
                          "node does not exist in abstraction graph")
    InsertEdge ledge@(src,tgt,edgelab) ->
      do let dg2abstrNodeMap = dg2abstrNode convMaps
         case (Map.lookup (libname,src) dg2abstrNodeMap,
               Map.lookup (libname,tgt) dg2abstrNodeMap) of
           (Just abstrSrc, Just abstrTgt) ->
             do let dgEdge = (libname, (src,tgt,showPretty edgelab ""))
                (Result descr err) <-
                   addlink gid (getDGLinkType edgelab)
                              "" (Just ledge) abstrSrc abstrTgt grInfo
                case err of
                  Nothing ->
                    do let newConvMaps = convMaps
                              {dg2abstrEdge =
                               Map.insert dgEdge descr (dg2abstrEdge convMaps),
                               abstr2dgEdge =
                               Map.insert descr dgEdge (abstr2dgEdge convMaps)}
                       applyChangesAux2 gid libname grInfo visibleNodes
                                 (descr+1) newConvMaps changes
                  Just msg ->
                   error ("applyChangesAux2: could not add link from "
                          ++ (show src) ++ " to " ++ (show tgt) ++ ":\n"
                          ++ (show msg))
           _ ->
               error ("applyChangesAux2: could not add link " ++ (show src)
                      ++ " to " ++ (show tgt) ++ ": illegal end nodes")


    DeleteEdge (src,tgt,edgelab) ->
      do let dgEdge = (libname, (src,tgt,showPretty edgelab ""))
             dg2abstrEdgeMap = dg2abstrEdge convMaps
         case Map.lookup dgEdge dg2abstrEdgeMap of
            Just abstrEdge ->
              do (Result descr err) <- dellink gid abstrEdge grInfo
                 case err of
                   Nothing ->
                     do let newConvMaps = convMaps
                                {dg2abstrEdge =
                                     Map.delete dgEdge dg2abstrEdgeMap,
                                 abstr2dgEdge =
                                     Map.delete abstrEdge (abstr2dgEdge
                                                           convMaps)}
                        applyChangesAux2 gid libname grInfo visibleNodes
                                 (descr+1) newConvMaps changes
                   Just msg -> error ("applyChangesAux2: could not delete edge "
                                      ++ (show abstrEdge) ++ ":\n"
                                      ++msg)

            Nothing -> error ("applyChangesAux2: deleted edge from "
                              ++ (show src) ++ " to " ++ (show tgt)
                              ++ " of type " ++ showPretty (dgl_type edgelab)
                              " and origin " ++ (show (dgl_origin edgelab))
                              ++ " of development "
                         ++ "graph does not exist in abstraction graph")


