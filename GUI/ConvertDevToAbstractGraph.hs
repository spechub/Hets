{- |
Module      :  $Header$
Description :  Central GUI for Hets, with display of development graph
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Conversion of development graphs from Logic.DevGraph
   to abstract graphs of the graph display interface

A composition table is used when abstracting the graph and composing
multiple edges. It looks like this

'[("normal","normal","normal"),
 ("normal","inclusion","normal"),
 ("inclusion","normal","normal"),
 ("inclusion","inclusion","inclusion")]'

A ginfo can be created with initgraphs. The graph is then created with
addnode and addlink.

-}


module GUI.ConvertDevToAbstractGraph 
    (convertGraph,GraphMem,ConversionMaps,initializeConverter)
    where

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
import Static.DGTranslation

import Proofs.EdgeUtils
import Proofs.InferBasic
import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.SimpleTheoremHideShift
--import Proofs.TheoremHideShift
import Proofs.StatusUtils

import GUI.AbstractGraphView as AGV
import GUI.ShowLogicGraph
import GUI.Utils
import qualified GUI.HTkUtils (displayTheory)
import GUI.ProofManagement (GUIMVar)
import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)
import GUI.DGTranslation

import FileDialog
import Broadcaster(newSimpleBroadcaster,applySimpleUpdate)
import Sources(toSimpleSource)
import DaVinciGraph
import GraphDisp
import GraphConfigure
import TextDisplay
import qualified HTk
import InfoBus

import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap
import Common.Id
import Common.DocUtils
import Common.Doc
import Common.Result as Res
import Common.ResultT

import qualified Common.InjMap as InjMap

import Driver.Options
import Driver.WriteFn
import Driver.ReadFn

import Data.Graph.Inductive.Graph as Graph
import Data.IORef
import Data.Maybe
import List(nub)
import Control.Monad
import Control.Monad.Trans
import Control.Concurrent.MVar
import Events
import DialogWin (useHTk)
import Messages

{- Maps used to track which node resp edge of the abstract graph
correspondes with which of the development graph and vice versa and
one Map to store which libname belongs to which development graph-}

data ConversionMaps = ConversionMaps {
			dgAndabstrNode :: DGraphAndAGraphNode,
			dgAndabstrEdge :: DGraphAndAGraphEdge,
                        libname2dg :: LibEnv} deriving Show

instance Pretty ConversionMaps where
  pretty convMaps =
       text "dg2abstrNode"
    $+$ pretty (InjMap.getAToB $ dgAndabstrNode convMaps)
    $+$ text "dg2abstrEdge"
    $+$ pretty (InjMap.getAToB $ dgAndabstrEdge convMaps)
    $+$ text "abstr2dgNode"
    $+$ pretty (InjMap.getBToA $ dgAndabstrNode convMaps)
    $+$ text "abstr2dgEdge"
    $+$ pretty (InjMap.getBToA $ dgAndabstrEdge convMaps)

data GraphMem = GraphMem {
                  graphInfo :: GraphInfo,
                  nextGraphId :: Descr}

-- | types of the Maps above 
type DGraphAndAGraphNode = InjMap.InjMap (LIB_NAME, Node) Descr
type DGraphAndAGraphEdge = InjMap.InjMap (LIB_NAME, (Descr, Descr, String)) Descr
data InternalNames =
     InternalNames { showNames :: Bool,
                     updater :: [(String,(String -> String) -> IO ())] }

data GInfo = GInfo 
             { libEnvIORef :: IORef LibEnv
             , descrIORef :: IORef Descr
             , conversionMapsIORef :: IORef ConversionMaps
             , graphId :: Descr 
             , gi_LIB_NAME :: LIB_NAME
             , gi_GraphInfo :: GraphInfo
             , internalNamesIORef :: IORef InternalNames -- show internal names?
             , gi_hetcatsOpts :: HetcatsOpts
             , visibleNodesIORef :: IORef [[Node]]
             , proofGUIMVar :: GUIMVar
             }

initializeConverter :: IO (IORef GraphMem,HTk.HTk)
initializeConverter =
    do wishInst <- HTk.initHTk [HTk.withdrawMainWin]
       showLogicGraph daVinciSort
       initGraphInfo <- initgraphs
       graphMem <- (newIORef GraphMem{nextGraphId = 0,
                                      graphInfo = initGraphInfo})
       return (graphMem,wishInst)

-- | converts the development graph given by its libname into an abstract
-- graph and returns the descriptor of the latter, the graphInfo it is
-- contained in and the conversion maps (see above)
convertGraph :: IORef GraphMem -> LIB_NAME -> LibEnv -> HetcatsOpts
             -> String  -- ^ title of graph
             -> IO (Descr, GraphInfo, ConversionMaps)
convertGraph graphMem libname libEnv opts title =
  do let convMaps = ConversionMaps
           {{-dg2abstrNode = Map.empty::DGraphToAGraphNode,
            abstr2dgNode = Map.empty::AGraphToDGraphNode,
            dg2abstrEdge = Map.empty::DGraphToAGraphEdge,
            abstr2dgEdge = Map.empty::AGraphToDGraphEdge,-}
	    dgAndabstrNode = InjMap.empty::DGraphAndAGraphNode,
	    dgAndabstrEdge = InjMap.empty::DGraphAndAGraphEdge,
            libname2dg = libEnv}

     case Map.lookup libname libEnv of
       Just gctx ->
        do let dgraph = devGraph gctx
           (abstractGraph,grInfo,convRef) <-
                  initializeGraph graphMem libname dgraph convMaps
                                  gctx opts title
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
                     -> String    -- ^ title of graph
                     -> IO (Descr,GraphInfo,IORef ConversionMaps)
initializeGraph ioRefGraphMem ln dGraph convMaps _ opts title = do
  graphMem <- readIORef ioRefGraphMem
  event <- newIORef 0
  convRef <- newIORef convMaps
  showInternalNames <- newIORef (InternalNames False [])
  ioRefProofStatus <- newIORef $ libname2dg convMaps
  ioRefSubtreeEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  ioRefVisibleNodes <- newIORef [(Graph.nodes dGraph)]
  guiMVar <- newEmptyMVar 
  let gid = nextGraphId graphMem
      actGraphInfo = graphInfo graphMem
      gInfo = GInfo {libEnvIORef = ioRefProofStatus, 
                     descrIORef = event, 
                     conversionMapsIORef = convRef, 
                     graphId = gid, 
                     gi_LIB_NAME = ln, 
                     gi_GraphInfo = actGraphInfo,
                     internalNamesIORef = showInternalNames, 
                     gi_hetcatsOpts = opts, 
                     visibleNodesIORef = ioRefVisibleNodes,
                     proofGUIMVar = guiMVar}
      file = libNameToFile opts ln ++ prfSuffix
  AGV.Result descr msg <-
    makegraph (title ++ " for " ++ show ln)
         -- action on "open"
             (do evnt <- fileDialogStr "Open..." file
                 maybeFilePath <- HTk.sync evnt
                 case maybeFilePath of
                   Just filePath ->
                           do openProofStatus ln filePath ioRefProofStatus
                                              convRef opts
                              return ()
                   Nothing -> fail "Could not open file."
              )
         -- action on "save"
             (  saveProofStatus ln file
                                   ioRefProofStatus opts)
         -- action on "save as...:"
             (  do evnt <- newFileDialogStr "Save as..." file
                   maybeFilePath <- HTk.sync evnt
                   case maybeFilePath of
                     Just filePath ->
                       saveProofStatus ln filePath ioRefProofStatus opts
                     Nothing -> fail "Could not save file."
             )
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
                          (do AGV.Result descr msg
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
                    ],
                  Menu (Just "Development Graph")
                  [
                   Button "Translation"
                          (openTranslateGraph (libname2dg convMaps) ln opts 
                                $ (getDGLogic (libname2dg convMaps)))
                  ]
                  ])]
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
                  ("hetproventhm",
                   GraphConfigure.Double $$$ Color "Green"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("hetunproventhm",
                   GraphConfigure.Double $$$ Color "Coral"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("hetlocalproventhm",
                   GraphConfigure.Double $$$ Color "Green"
                   $$$ createLocalEdgeMenuThmEdge gInfo
                   $$$ createLocalMenuValueTitleShowConservativity
                   $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue),
                  ("hetlocalunproventhm",
                   GraphConfigure.Double $$$ Color "Coral"
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

saveProofStatus :: LIB_NAME -> FilePath -> IORef LibEnv -> HetcatsOpts -> IO ()
saveProofStatus ln file ioRefProofStatus opts = encapsulateWaitTermAct $ do
    proofStatus <- readIORef ioRefProofStatus
    writeShATermFile file (ln, lookupHistory ln proofStatus)
    putIfVerbose opts 2 $ "Wrote " ++ file

-- | implementation of open menu, read in a proof status
openProofStatus :: LIB_NAME -> FilePath -> IORef LibEnv
                -> IORef ConversionMaps
                -> HetcatsOpts -> IO (Descr, GraphInfo, ConversionMaps)
openProofStatus ln file ioRefProofStatus convRef opts = do
    mh <- readVerbose opts ln file
    case mh of
      Nothing -> fail
                 $ "Could not read proof status from file '"
                       ++ file ++ "'"
      Just h -> do
          let libfile = libNameToFile opts ln
          m <- anaLib opts libfile
          case m of
            Nothing -> fail
                 $ "Could not read original development graph from '"
                       ++ libfile ++  "'"
            Just (_, libEnv) -> case Map.lookup ln libEnv of
                Nothing -> fail
                 $ "Could not get original development graph for '"
                       ++ showDoc ln "'"
                Just gctx -> do
                    oldEnv <- readIORef ioRefProofStatus
                    let proofStatus = Map.insert ln
                                      (applyProofHistory h gctx) oldEnv
                    writeIORef ioRefProofStatus proofStatus
                    initGraphInfo <- initgraphs
                    graphMem' <- (newIORef GraphMem{nextGraphId = 0,
                                      graphInfo = initGraphInfo})
                    (gid, actGraphInfo, convMaps)
                          <- convertGraph graphMem' ln proofStatus opts
                                  "Proof Status "
                    writeIORef convRef convMaps
                    redisplay gid actGraphInfo
                    return (gid, actGraphInfo, convMaps)

-- | apply a rule of the development graph calculus
proofMenu :: GInfo
             -> (LibEnv -> IO (Res.Result LibEnv))
             -> IO ()
proofMenu (GInfo {libEnvIORef = ioRefProofStatus, 
                  descrIORef = event, 
                  conversionMapsIORef = convRef, 
                  graphId = gid, 
                  gi_LIB_NAME = ln, 
                  gi_GraphInfo = actGraphInfo,
                  gi_hetcatsOpts = hOpts, 
                  proofGUIMVar = guiMVar,
                  visibleNodesIORef = ioRefVisibleNodes}) proofFun = do
  filled <- tryPutMVar guiMVar Nothing
  if not filled
     then readMVar guiMVar >>=
                  (maybe (putIfVerbose hOpts 4 "proofMenu: ignored Nothing") 
                         (\ w -> do 
                             putIfVerbose hOpts 4 $ 
                                  "proofMenu: Ignored Proof command; "++
                                  "maybe a proof window is still open?"
                             HTk.putWinOnTop w))
     else do
        proofStatus <- readIORef ioRefProofStatus
        putIfVerbose hOpts 4 "Proof started via \"Proofs\" menu"
        Res.Result ds res <- proofFun proofStatus
        putIfVerbose hOpts 4 "Analyzing result of proof"
        case res of
          Nothing -> mapM_ (putStrLn . show) ds
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
             mGUIMVar <- tryTakeMVar guiMVar
             maybe (fail $ "should be filled with Nothing after "++
                        "proof attempt")
                   (const $ return ())
                   mGUIMVar

proofMenuSef :: GInfo -> (LibEnv -> LibEnv) -> IO ()
proofMenuSef gInfo proofFun = proofMenu gInfo (return . return . proofFun)

-- -------------------------------------------------------------
-- methods to create the local menus of the different nodetypes
-- -------------------------------------------------------------

type NodeDescr = (String, Descr, Descr)

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec :: String -> IORef (Map.Map Descr Descr)
                            -> GraphInfo -> IORef GraphMem -> GInfo
                            -> DaVinciNodeTypeParms NodeDescr
createLocalMenuNodeTypeSpec color ioRefSubtreeEvents actGraphInfo
             ioRefGraphMem 
             gInfo@(GInfo {conversionMapsIORef = convRef,
                           visibleNodesIORef = ioRefVisibleNodes}) =
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
                  -- >$$$ LocalMenu (Button "xxx" error "GUI.ConvertAbstractToDevGraph")
                  $$$ emptyNodeTypeParms

-- | local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal :: String -> GInfo
                                -> DaVinciNodeTypeParms NodeDescr
createLocalMenuNodeTypeInternal color
               gInfo@(GInfo {internalNamesIORef = showInternalNames}) =
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

-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef :: String -> GraphInfo -> IORef GraphMem
                             -> GraphMem -> GInfo
                             -> DaVinciNodeTypeParms NodeDescr
createLocalMenuNodeTypeDgRef color actGraphInfo
                             ioRefGraphMem graphMem
                             gInfo =
                 Box $$$ Color color
                 $$$ ValueTitle (\ (s,_,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSignature gInfo,
                    createLocalMenuButtonShowTheory gInfo,
                    createLocalMenuButtonProveAtNode gInfo,
                    createLocalMenuButtonShowProofStatusOfNode gInfo,
                    createLocalMenuButtonShowNumberOfNode,
                    createLocalMenuButtonShowNumberOfRefNode gInfo,
                    Button "Show referenced library"
                     (\ (_, descr, gid) ->
                        do convMaps <- readIORef $ conversionMapsIORef gInfo
                           (refDescr, newGraphInfo, _) <-
                                showReferencedLibrary ioRefGraphMem descr
                                              gid
                                              actGraphInfo
                                              convMaps
                                              (gi_hetcatsOpts gInfo)
--writeIORef convRef newConvMaps
                           writeIORef ioRefGraphMem
                                      graphMem{graphInfo = newGraphInfo,
                                               nextGraphId = refDescr +1}
                           redisplay refDescr newGraphInfo
                           return ()
                     )])
                 $$$ emptyNodeTypeParms

type ButtonMenu a = MenuPrim (Maybe String) (a -> IO ())

-- | menu button for local menus
createMenuButton :: String -> (Descr -> DGraphAndAGraphNode -> DGraph -> IO ())
                 -> GInfo -> ButtonMenu NodeDescr
createMenuButton title menuFun gInfo =
                    (Button title
                      (\ (_, descr, _) ->
                        do convMaps <- readIORef $ conversionMapsIORef gInfo
                           ps <- readIORef $ libEnvIORef gInfo
                           let dGraph = lookupDGraph (gi_LIB_NAME gInfo) ps
                           menuFun descr
                                   (dgAndabstrNode convMaps)
                                   dGraph
                           return ()
                       )
                    )

createLocalMenuButtonShowSpec :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowSpec = createMenuButton "Show spec" showSpec

createLocalMenuButtonShowSignature :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowSignature =
    createMenuButton "Show signature" getSignatureOfNode

createLocalMenuButtonShowTheory :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowTheory gInfo =
    createMenuButton "Show theory" (getTheoryOfNode gInfo) gInfo

createLocalMenuButtonShowLocalAx :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowLocalAx gInfo =
  createMenuButton "Show local axioms" (getLocalAxOfNode gInfo) gInfo

createLocalMenuButtonTranslateTheory :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonTranslateTheory gInfo =
  createMenuButton "Translate theory" (translateTheoryOfNode gInfo) gInfo

{- |
   create a sub Menu for taxonomy visualisation
   (added by KL)
-}
createLocalMenuTaxonomy :: GInfo -> ButtonMenu NodeDescr
createLocalMenuTaxonomy ginfo =
      (Menu (Just "Taxonomy graphs")
       [createMenuButton "Subsort graph"
               (passTh displaySubsortGraph) ginfo,
        createMenuButton "Concept graph"
               (passTh displayConceptGraph) ginfo])
    where passTh displayFun descr ab2dgNode dgraph =
              do r <- lookupTheoryOfNode (libEnvIORef ginfo)
                                         descr ab2dgNode dgraph
                 case r of
                  Res.Result [] (Just (n, gth)) ->
                      displayFun (showDoc n "") gth
                  Res.Result ds _ ->
                     showDiags defaultHetcatsOpts ds

createLocalMenuButtonShowSublogic :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowSublogic gInfo =
  createMenuButton "Show sublogic" 
                   (getSublogicOfNode $ libEnvIORef gInfo) gInfo

createLocalMenuButtonShowNodeOrigin :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowNodeOrigin  =
  createMenuButton "Show origin" showOriginOfNode

createLocalMenuButtonShowProofStatusOfNode :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowProofStatusOfNode gInfo =
  createMenuButton "Show proof status" (showProofStatusOfNode gInfo) gInfo

createLocalMenuButtonProveAtNode :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonProveAtNode gInfo =
  createMenuButton "Prove" (proveAtNode False gInfo) gInfo

createLocalMenuButtonCCCAtNode :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (proveAtNode True gInfo) gInfo

createLocalMenuButtonShowJustSubtree :: IORef (Map.Map Descr Descr)
    -> IORef ConversionMaps -> IORef [[Node]] -> IORef GraphMem -> GraphInfo
    -> ButtonMenu NodeDescr
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


createLocalMenuButtonUndoShowJustSubtree :: IORef [[Node]]
    -> IORef (Map.Map Descr Descr) -> GraphInfo -> ButtonMenu NodeDescr
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

createLocalMenuButtonShowIDOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowIDOfEdge _ =
  (Button "Show ID of this edge"
                      (\ (_,descr,maybeLEdge)  ->
                        do showIDOfEdge descr maybeLEdge
                           return ()
                       ))

createLocalMenuButtonShowNumberOfNode :: ButtonMenu NodeDescr
createLocalMenuButtonShowNumberOfNode =
  (Button "Show number of node"
    (\ (_, descr, _) ->
       getNumberOfNode descr))

createLocalMenuButtonShowNumberOfRefNode :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowNumberOfRefNode =
    createMenuButton "Show number of referenced node" getNumberOfRefNode

getNumberOfRefNode :: Descr -> DGraphAndAGraphNode -> DGraph -> IO()
getNumberOfRefNode descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just (_, node) ->
      let dgnode = lab' (context dgraph node)
          title = "Number of node"
       in createTextDisplay title (show (dgn_node dgnode)) [HTk.size(10,10)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")


-- -------------------------------------------------------------
-- methods to create the local menus for the edges
-- -------------------------------------------------------------

createLocalEdgeMenu :: GInfo -> LocalMenu EdgeValue
createLocalEdgeMenu gInfo =
    LocalMenu (Menu (Just "edge menu")
               [createLocalMenuButtonShowIDOfEdge gInfo,
		createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo]
              )

createLocalEdgeMenuThmEdge :: GInfo -> LocalMenu EdgeValue
createLocalEdgeMenuThmEdge gInfo =
   LocalMenu (Menu (Just "thm egde menu")
              [	createLocalMenuButtonShowIDOfEdge gInfo,
		createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonShowProofStatusOfThm gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo]
              )

createLocalMenuButtonShowMorphismOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowMorphismOfEdge _ =
  (Button "Show morphism"
                      (\ (_,descr,maybeLEdge)  ->
                        do showMorphismOfEdge descr maybeLEdge
                           return ()
                       ))

createLocalMenuButtonShowOriginOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowOriginOfEdge _ =
    (Button "Show origin"
         (\ (_,descr,maybeLEdge) ->
           do showOriginOfEdge descr maybeLEdge
              return ()
          ))

createLocalMenuButtonCheckconservativityOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonCheckconservativityOfEdge gInfo =
    (Button "Check conservativity (preliminary)"
                      (\ (_, descr, maybeLEdge)  ->
                        do checkconservativityOfEdge descr gInfo maybeLEdge
                           return ()
                       ))

createLocalMenuButtonShowProofStatusOfThm :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowProofStatusOfThm _ =
   (Button "Show proof status"
        (\ (_,descr,maybeLEdge) ->
          do showProofStatusOfThm descr maybeLEdge
             return ()
         ))

createLocalMenuValueTitleShowConservativity :: ValueTitle EdgeValue
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

showSpec :: Descr -> DGraphAndAGraphNode -> DGraph -> IO ()
showSpec descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
   Nothing -> return ()
   Just (_, node) -> do
      let sp = dgToSpec dgraph node
      putStrLn $ case sp of
            Res.Result ds Nothing -> show $ vcat $ map pretty ds
            Res.Result _ m -> showDoc m ""

{- | auxiliary method for debugging. shows the number of the given node
     in the abstraction graph -}
getNumberOfNode :: Descr -> IO()
getNumberOfNode descr =
  let title = "Number of node"
-- make the node number consistent
    in createTextDisplay title (showDoc (descr-1) "") [HTk.size(10,10)]

{- | outputs the signature of a node in a window;
used by the node menu defined in initializeGraph -}
-- lllllllllllllllllllllllllllllll
getSignatureOfNode :: Descr -> DGraphAndAGraphNode -> DGraph -> IO()
getSignatureOfNode descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just (_, node) ->
      let dgnode = lab' (context dgraph node)
          title = "Signature of "++showName (dgn_name dgnode)
       in createTextDisplay title (showDoc (dgn_sign dgnode) "")
                            [HTk.size(80,50)]
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

{- |
   fetches the theory from a node inside the IO Monad
   (added by KL based on code in getTheoryOfNode) -}
lookupTheoryOfNode :: IORef LibEnv -> Descr -> DGraphAndAGraphNode ->
                      DGraph -> IO (Res.Result (Node,G_theory))
lookupTheoryOfNode proofStatusRef descr dgAndabstrNodeMap _ = do
 libEnv <- readIORef proofStatusRef
 case (do
  (ln, node) <-
        maybeToResult nullRange ("Node "++show descr++" not found")
                       $ InjMap.lookupWithB descr dgAndabstrNodeMap
  gth <- computeTheory libEnv ln node
  return (node, gth)
    ) of
   r -> do
         return r

{- | outputs the local axioms of a node in a window;
used by the node menu defined in initializeGraph-}
getLocalAxOfNode :: GInfo -> Descr -> DGraphAndAGraphNode -> DGraph -> IO()
getLocalAxOfNode _ descr dgAndabstrNodeMap dgraph = do
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
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
getTheoryOfNode :: GInfo -> Descr -> DGraphAndAGraphNode -> DGraph -> IO()
getTheoryOfNode gInfo descr dgAndabstrNodeMap dgraph = do
 r <- lookupTheoryOfNode (libEnvIORef gInfo) descr dgAndabstrNodeMap dgraph
 case r of
  Res.Result ds res -> do
    showDiags (gi_hetcatsOpts gInfo) ds
    case res of
      (Just (n, gth)) -> displayTheory ((addHasInHidingWarning dgraph n)++"Theory") n dgraph gth
      _ -> return ()

displayTheory :: String -> Node -> DGraph -> G_theory
              -> IO ()
displayTheory ext node dgraph gth =
     GUI.HTkUtils.displayTheory ext
        (showName $ dgn_name $ lab' (context dgraph node))
        gth

addHasInHidingWarning :: DGraph -> Node -> String
addHasInHidingWarning dgraph n 
     | hasIncomingHidingEdge dgraph n =
           "< Warning: this node has incoming hiding links ! >\n"
     | otherwise = ""      

{- | translate the theory of a node in a window;
used by the node menu defined in initializeGraph-}
translateTheoryOfNode :: GInfo -> Descr -> DGraphAndAGraphNode -> DGraph -> IO()
translateTheoryOfNode gInfo@(GInfo {gi_hetcatsOpts = opts})
                      descr dgAndabstrNodeMap dgraph = do
 libEnv <- readIORef $ libEnvIORef gInfo
 case (do
   (ln, node) <-
        maybeToResult nullRange ("Node "++show descr++" not found")
                       $ InjMap.lookupWithB descr dgAndabstrNodeMap
   th <- computeTheory libEnv ln node
   return (node,th) ) of
  Res.Result [] (Just (node,th)) -> do
    Res.Result ds _ <-  runResultT(
      do G_theory lid sign _ sens _ <- return th
         -- find all comorphism paths starting from lid
         let paths = findComorphismPaths logicGraph (sublogicOfTh th)
         -- let the user choose one
         sel <- lift $ listBox "Choose a logic translation"
                   (map show paths)
         i <- case sel of
           Just j -> return j
           _ -> liftR $ fail "no logic translation chosen"
         Comorphism cid <- return (paths!!i)
         -- adjust lid's
         let lidS = sourceLogic cid
             lidT = targetLogic cid
         sign' <- coerceSign lid lidS "" sign
         sens' <- coerceThSens lid lidS "" sens
         -- translate theory along chosen comorphism
         (sign'',sens1) <-
             liftR $ wrapMapTheory cid (sign', toNamedList sens')
         lift $ displayTheory "Translated theory" node dgraph
            (G_theory lidT sign'' 0 (toThSens sens1) 0)
     )
    showDiags opts ds
    return ()
  Res.Result ds _ -> showDiags opts ds

{- | outputs the sublogic of a node in a window;
used by the node menu defined in initializeGraph-}
----------------------------------------------------------
getSublogicOfNode :: IORef LibEnv -> Descr -> DGraphAndAGraphNode
                  -> DGraph -> IO()
getSublogicOfNode proofStatusRef descr dgAndabstrNodeMap dgraph = do
  libEnv <- readIORef proofStatusRef
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just (ln, node) ->
      let dgnode = lab' (context dgraph node)
          name = case dgnode of
                       (DGNode nname _ _ _ _ _ _) -> nname
                       _ -> emptyNodeName
       in case computeTheory libEnv ln node of
        Res.Result _ (Just th) ->
                let logstr = show $ sublogicOfTh th
                    title =  "Sublogic of "++showName name
                 in createTextDisplay title logstr [HTk.size(30,10)]
        Res.Result ds _ ->
          error ("Could not compute theory for sublogic computation: "++
                concatMap show ds)
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

-- | prints the origin of the node
showOriginOfNode :: Descr -> DGraphAndAGraphNode -> DGraph -> IO()
showOriginOfNode descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just (_, node) ->
      do let dgnode = lab' (context dgraph node)
         case dgnode of
           DGNode name _ _ _ orig _ _ ->
              let title =  "Origin of node "++showName name
               in createTextDisplay title
                    (showDoc orig "") [HTk.size(30,10)]
           DGRef _ _ _ _ _ _ -> error "showOriginOfNode: no DGNode"
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

-- | Show proof status of a node
showProofStatusOfNode :: GInfo -> Descr -> DGraphAndAGraphNode -> DGraph -> IO()
showProofStatusOfNode _ descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
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
  G_theory _ _ _ sens _ ->
     let goals = OMap.filter (not . isAxiom) sens
         (proven,open) = OMap.partition isProvenSenStatus goals
      in "Proven proof goals:\n"
         ++ showDoc proven ""
         ++ if not $ hasOpenConsStatus True dgnode
             then showDoc (dgn_cons_status dgnode)
                      "is the conservativity status of this node"
             else ""
         ++ "\nOpen proof goals:\n"
         ++ showDoc open ""
         ++ if hasOpenConsStatus False dgnode
             then showDoc (dgn_cons_status dgnode)
                      "should be the conservativity status of this node"
             else ""

-- | start local theorem proving or consistency checking at a node
proveAtNode :: Bool -> GInfo -> Descr -> DGraphAndAGraphNode -> DGraph -> IO()
proveAtNode checkCons 
            gInfo@(GInfo {gi_LIB_NAME = ln,
                         proofGUIMVar = guiMVar}) descr dgAndabstrNodeMap _ =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just libNode -> proofMenu gInfo (basicInferenceNode checkCons logicGraph 
                                                        libNode ln guiMVar)
    Nothing -> error ("node with descriptor "
                      ++ (show descr)
                      ++ " has no corresponding node in the development graph")

-- | print the id of the edge
showIDOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showIDOfEdge _ (Just (_, _, linklab)) =
      createTextDisplay "ID of Edge" (show $ dgl_id linklab) [HTk.size(30,10)] 
showIDOfEdge descr Nothing =
      createTextDisplay "Error"
          ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph") [HTk.size(30,10)]

-- | print the morphism of the edge
showMorphismOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showMorphismOfEdge _ (Just (_,_,linklab)) =
      createTextDisplay "Signature morphism"
           ((showDoc (dgl_morphism linklab) "")++hidingMorph)
           [HTk.size(100,40)]
  where
    hidingMorph = case (dgl_type linklab) of
                    (HidingThm morph _) -> "\n ++++++ \n"
                                           ++ (showDoc morph "")
                    _ -> ""
showMorphismOfEdge descr Nothing =
      createTextDisplay "Error"
          ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph") [HTk.size(30,10)]


-- | print the origin of the edge
showOriginOfEdge :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showOriginOfEdge _ (Just (_,_,linklab)) =
      createTextDisplay "Origin of link"
        (showDoc (dgl_origin linklab) "")  [HTk.size(30,10)]
showOriginOfEdge descr Nothing =
      createTextDisplay "Error"
         ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph") [HTk.size(30,10)]

-- | print the proof base of the edge
showProofStatusOfThm :: Descr -> Maybe (LEdge DGLinkLab) -> IO()
showProofStatusOfThm _ (Just ledge) =
    createTextSaveDisplay "Proof Status" "proofstatus.txt"
         (showDoc (getProofStatusOfThm ledge) "\n")
showProofStatusOfThm descr Nothing =
    putStrLn ("edge "++(show descr)++" has no corresponding edge"
                ++ "in the development graph")

-- | check conservativity of the edge
checkconservativityOfEdge :: Descr -> GInfo -> Maybe (LEdge DGLinkLab) -> IO()
checkconservativityOfEdge _ gInfo
                           (Just (source,target,linklab)) = do
  libEnv <- readIORef $ libEnvIORef gInfo
  let dgraph = lookupDGraph (gi_LIB_NAME gInfo) libEnv
      dgtar = lab' (context dgraph target)
  case dgtar of
    DGNode _ (G_theory lid _ _ sens _) _ _ _ _ _ ->
     case dgl_morphism linklab of
     GMorphism cid _ _ morphism2 _ -> do
      morphism2' <- coerceMorphism (targetLogic cid) lid
                   "checkconservativityOfEdge" morphism2
      let th = case computeTheory libEnv (gi_LIB_NAME gInfo) source of
                Res.Result _ (Just th1) -> th1
                _ -> error "checkconservativityOfEdge: computeTheory"
      G_theory lid1 sign1 _ sens1 _ <- return th
      sign2 <- coerceSign lid1 lid "checkconservativityOfEdge.coerceSign" sign1
      sens2 <- coerceThSens lid1 lid "" sens1
      let Res.Result ds res =
                     conservativityCheck lid (sign2, toNamedList sens2)
                                         morphism2' $ toNamedList sens
          showRes = case res of
                   Just(Just True) -> "The link is conservative"
                   Just(Just False) -> "The link is not conservative"
                   _ -> "Could not determine whether link is conservative"
          myDiags = unlines (map show ds)
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
-- lllllllllllllllllllllll
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
     AGV.Result newDescr _ <- addnode descr
                                nodetype
                                (getDGNodeName dgnode)
                                grInfo
     convertNodesAux convMaps 
       { dgAndabstrNode = InjMap.insert (libname, node) newDescr 
                          (dgAndabstrNode convMaps)
       } descr grInfo lNodes libname

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
  do let srcnode = InjMap.lookupWithA (libname,src) (dgAndabstrNode convMaps)
         tarnode = InjMap.lookupWithA (libname,tar) (dgAndabstrNode convMaps)
     case (srcnode,tarnode) of
      (Just s, Just t) -> do
        AGV.Result newDescr msg <- addlink descr (getDGLinkType edgelab)
                                   "" (Just ledge) s t grInfo
        case msg of
          Nothing -> return ()
          Just err -> fail err
        newConvMaps <- convertEdgesAux convMaps 
            { dgAndabstrEdge = InjMap.insert (libname,
				              (src, tar, showDoc edgelab ""))
                  newDescr (dgAndabstrEdge convMaps)
	    } descr grInfo lEdges libname
        return newConvMaps
      _ -> error "Cannot find nodes"

-- | show library referened by a DGRef node (=node drawn as a box)
showReferencedLibrary :: IORef GraphMem -> Descr -> Descr -> GraphInfo
                      -> ConversionMaps -> HetcatsOpts
                      -> IO (Descr, GraphInfo, ConversionMaps)
showReferencedLibrary graphMem descr _ _ convMaps opts =
  case InjMap.lookupWithB descr (dgAndabstrNode convMaps) of
    Just (libname,node) ->
         case Map.lookup libname libname2dgMap of
          Just gctx ->
            do let dgraph = devGraph gctx
                   (_,(DGRef _ refLibname _ _ _ _)) =
                       labNode' (context dgraph node)
               case Map.lookup refLibname libname2dgMap of
                 Just _ ->
                     convertGraph graphMem refLibname (libname2dg convMaps)
                                  opts "development graph"
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
-- 
showJustSubtree :: IORef GraphMem -> Descr -> Descr -> ConversionMaps
                -> [[Node]]-> IO (Descr, [[Node]], Maybe String)
showJustSubtree ioRefGraphMem descr abstractGraph convMaps visibleNodes =
  case InjMap.lookupWithB descr (dgAndabstrNode convMaps) of
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
             AGV.Result eventDescr errorMsg <- hidenodes abstractGraph
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
  --case Map.lookup (libname,node) (dg2abstrNode convMaps) of
    case InjMap.lookupWithA (libname, node) (dgAndabstrNode convMaps) of
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
  --trace (concat $ map showDGRule (fst historyElem)) $ 
	applyChangesAux gid libname grInfo ioRefVisibleNodes
        (eventDescr, convMaps) changes
  where changes = removeContraryChanges (snd historyElem)

{-
showDGRule :: DGRule -> String
showDGRule TheoremHideShift = "TheoremHideShift "
showDGRule (HideTheoremShift _) = "HideTheoremShift "
showDGRule Borrowing = "Borrowing "
showDGRule ConsShift = "ConsShift "
showDGRule DefShift = "DefShift "
showDGRule MonoShift = "MonoShift "
showDGRule DefToMono = "DefToMono "
showDGRule MonoToCons = "MonoToCons "
showDGRule FreeIsMono = "FreeIsMono "
showDGRule MonoIsFree = "MonoIsFree "
showDGRule (GlobDecomp _) = "GlobDecomp "
showDGRule (LocDecomp _) = "LocalDecomp "
showDGRule (LocInference _) = "LocInference "
showDGRule (GlobSubsumption _) = "GlobSubsumption "
showDGRule (Composition _) = "Composition "
showDGRule LocalInference = "LocalInference "
showDGRule (BasicInference _ _) = "BasicInference "
showDGRule (BasicConsInference _ _) = "BasicConsInference "
-}

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
      {-trace (show $ dgAndabstrEdge newConvMaps) $-} 
      writeIORef ioRefVisibleNodes newVisibleNodes
      return (newEventDescr, newConvMaps)

-- | auxiliary function for applyChanges
applyChangesAux2 :: Descr -> LIB_NAME -> GraphInfo -> [[Node]] -> Descr
                  -> ConversionMaps -> [DGChange]
                  -> IO ([[Node]], Descr, ConversionMaps)
applyChangesAux2  _ _ _ visibleNodes eventDescr convMaps [] =
  return (visibleNodes, eventDescr+1, convMaps)
applyChangesAux2 gid libname grInfo visibleNodes _ convMaps (change:changes) =
  case change of
    SetNodeLab (node, newLab) -> do
      let nodetype = getDGNodeType newLab
	  nodename = getDGNodeName newLab
	  dgNode = (libname, node)
      case InjMap.lookupWithA dgNode (dgAndabstrNode convMaps) of
	   Just abstrNode -> do
		AGV.Result descr err <- 
		     changeNodeType gid abstrNode nodetype grInfo
		case err of
		     Nothing -> do
			 let newConvMaps = convMaps {dgAndabstrNode = InjMap.updateBWithA dgNode descr (dgAndabstrNode convMaps)}
			       {-
				dg2abstrNode =
				       Map.insert dgNode descr (dg2abstrNode convMaps),
				abstr2dgNode =
				       Map.insert descr dgNode (abstr2dgNode convMaps),
				dgAndabstrNode = InjMap.insert dgNode descr (dgAndabstrNode convMaps)
				-}     
		         applyChangesAux2 gid libname grInfo visibleNodes (descr+1) newConvMaps changes
		     Just msg ->
			  error ("applyChangesAux2: could not set node " ++ (show node)
			  ++" with name " ++ (show (nodename)) ++ "\n"
			  ++ msg)
	   Nothing -> error ("applyChangesAux2: could not set node "
                          ++ (show node) ++ " with name "
                          ++ (show nodename) ++": " ++
                          "node does not exist in abstraction graph")    
    InsertNode (node, nodelab) -> do
      let nodetype = getDGNodeType nodelab
          nodename = getDGNodeName nodelab
      AGV.Result descr err <-
          addnode gid nodetype nodename grInfo
      case err of
        Nothing ->
          do let dgNode = (libname,node)
                 newVisibleNodes = map (node :) visibleNodes
                 newConvMaps =
                     convMaps {{-dg2abstrNode =
                               Map.insert dgNode descr (dg2abstrNode convMaps),
                               abstr2dgNode =
                               Map.insert descr dgNode (abstr2dgNode convMaps),-}
			       dgAndabstrNode = InjMap.insert dgNode descr (dgAndabstrNode convMaps)
			       }
             applyChangesAux2 gid libname grInfo newVisibleNodes (descr+1)
                             newConvMaps changes
        Just msg ->
               error ("applyChangesAux2: could not add node " ++ (show node)
                      ++" with name " ++ (show (nodename)) ++ "\n"
                      ++ msg)
    DeleteNode (node, nodelab) -> do
      let nodename = getDGNodeName nodelab
          dgnode = (libname,node)
      case InjMap.lookupWithA dgnode (dgAndabstrNode convMaps) of
        Just abstrNode -> do
          AGV.Result descr err <- delnode gid abstrNode grInfo
          case err of
            Nothing -> do
                let newVisibleNodes = map (filter (/= node)) visibleNodes
                    newConvMaps =
                        convMaps {{-dg2abstrNode =
                                  Map.delete dgnode (dg2abstrNode convMaps),
                                  abstr2dgNode =
                                  Map.delete abstrNode (abstr2dgNode convMaps),-}
				  dgAndabstrNode = InjMap.delete dgnode abstrNode (dgAndabstrNode convMaps)
				  }
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
      do let dgAndabstrNodeMap = dgAndabstrNode convMaps
	 --let dg2abstrNodeMap = dg2abstrNode convMaps
	 case (InjMap.lookupWithA (libname, src) dgAndabstrNodeMap, InjMap.lookupWithA (libname, tgt) dgAndabstrNodeMap) of
         --case (Map.lookup (libname,src) dg2abstrNodeMap,
           --    Map.lookup (libname,tgt) dg2abstrNodeMap) of
           (Just abstrSrc, Just abstrTgt) ->
             do let dgEdge = (libname, (src,tgt,showDoc edgelab ""))
                {-
		case (InjMap.lookupWithA dgEdge $ dgAndabstrEdge convMaps) of
		    Just x -> case trace (show dgEdge) $ (InjMap.lookupWithB x $ dgAndabstrEdge convMaps) of
				   Just y -> putStrLn $ show y
				   Nothing -> putStr ""
--trace (show $ isProven ledge) $ putStrLn $ show x
		    _ -> putStr ""
		-}
		AGV.Result descr err <-
                   addlink gid (getDGLinkType edgelab)
                              "" (Just ledge) abstrSrc abstrTgt grInfo
                case err of
                  Nothing ->
                    do let newConvMaps = convMaps
                              {{-dg2abstrEdge =
                               Map.insert dgEdge descr (dg2abstrEdge convMaps),
                               abstr2dgEdge =
                               Map.insert descr dgEdge (abstr2dgEdge convMaps),-}
			       dgAndabstrEdge = InjMap.insert dgEdge descr (dgAndabstrEdge convMaps)
			       }
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
      do let dgEdge = (libname, (src,tgt,showDoc edgelab ""))
	     dgAndabstrEdgeMap = dgAndabstrEdge convMaps
 --trace (show $ InjMap.getAToB dgAndabstrEdgeMap) $ 
	 case (InjMap.lookupWithA dgEdge dgAndabstrEdgeMap) of
	 --  dg2abstrEdgeMap = dg2abstrEdge convMaps
         --case Map.lookup dgEdge dg2abstrEdgeMap of
            Just abstrEdge ->
              do AGV.Result descr err <- dellink gid abstrEdge grInfo
                 case err of
                   Nothing ->
                     do let newConvMaps = convMaps
                                {
				 {-dg2abstrEdge =
                                     Map.delete dgEdge (dg2abstrEdge convMaps),
                                 abstr2dgEdge =
                                     Map.delete abstrEdge (abstr2dgEdge convMaps),-}
				 dgAndabstrEdge = 
				     InjMap.delete dgEdge abstrEdge (dgAndabstrEdge convMaps)
				 }
                        applyChangesAux2 gid libname grInfo visibleNodes
                                 (descr+1) newConvMaps changes
                   Just msg -> error $ 
                               "applyChangesAux2: could not delete edge "
                                      ++ shows abstrEdge ":\n" ++ msg
{-trace ((show $ InjMap.getAToB dgAndabstrEdgeMap)++ "\nThe to be deleted edge is:\n" ++(show dgEdge)) $ -}
            Nothing -> error $ "applyChangesAux2: deleted edge from "
                              ++ shows src " to " ++ shows tgt
                              " of type " ++ showDoc (dgl_type edgelab)
                              " and origin " ++ shows (dgl_origin edgelab)
                              " of development "
                         ++ "graph does not exist in abstraction graph"

-- | display a window of translated graph with maximal sublogic.
openTranslateGraph :: LibEnv
                   -> LIB_NAME
                   -> HetcatsOpts 
                   -> Res.Result G_sublogics
                   -> IO ()
openTranslateGraph  libEnv ln opts (Res.Result diagsSl mSublogic) =
    -- if a error existed by the search of maximal sublogicn 
    -- (see GUI.DGTranslation.getDGLogic), the process need not to go on.
    if hasErrors diagsSl then
        do errorMess (unlines $ map show $ 
                           filter (relevantDiagKind . diagKind) diagsSl) 
           -- return ()
       else 
         do case mSublogic of 
             Just sublogic -> do
                 let paths = findComorphismPaths logicGraph sublogic
                 if null paths then
                     do errorMess "This graph has no comorphism to translation."
                   else do
                       Res.Result diagsR i <- runResultT ( do
                         -- the user choose one
                         sel <- lift $ listBox "Choose a logic translation"
                                (map show paths)
                         case sel of
                           Just j -> return j
                           _ -> liftR $ fail "no logic translation chosen"
                                                         )
                       aComor <- return (paths!!(fromJust i))
                       -- graph translation.
                       case libEnv_translation libEnv aComor of
                         Res.Result diagsTrans (Just newLibEnv) ->
                             do showDiags opts (diagsSl ++ diagsR ++ diagsTrans)
                                if hasErrors (diagsR ++ diagsTrans) then
                                    errorMess (unlines $ map show $ 
                                              filter (relevantDiagKind . diagKind)
                                                             (diagsR ++ diagsTrans))
                                  else dg_showGraphAux 
                                   (\gm -> convertGraph gm ln newLibEnv opts 
                                                    "translation Graph")
                         Res.Result diagsTrans Nothing ->
                             do errorMess (unlines $ map show $ 
                                               filter  (relevantDiagKind . diagKind)
                                                 (diagsSl ++ diagsR ++ diagsTrans))
                                return ()
             Nothing -> do errorMess "the maximal sublogic is not found."
                           return ()
  where relevantDiagKind Error = True
        relevantDiagKind Warning = (verbose opts) >= 2
        relevantDiagKind Hint = (verbose opts) >= 4
        relevantDiagKind Debug  = (verbose opts) >= 5
        relevantDiagKind MessageW = False


dg_showGraphAux :: (IORef GraphMem -> IO (Descr, GraphInfo, ConversionMaps))
                -> IO ()
dg_showGraphAux convFct = do
--  wishInst <- HTk.initHTk [HTk.withdrawMainWin]
  initGraphInfo <- initgraphs
  graphMem <- (newIORef GraphMem{nextGraphId = 0,
                                 graphInfo = initGraphInfo})
  useHTk    -- All messages are displayed in TK dialog windows
            -- from this point on
  (gid, gv, _cmaps) <- convFct graphMem
  redisplay gid gv
  return ()


