{- |
Module      :  $Header$
Description :  Menu creation functions for the Graphdisplay
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}
module GUI.GraphMenu
  (createGraph)
  where

import GUI.AbstractGraphView as AGV
import GUI.GraphTypes
import GUI.GraphLogic
import GUI.ShowLogicGraph(showLogicGraph)

import Static.DevGraph

import Proofs.Automatic(automatic)
import Proofs.Global(globSubsume, globDecomp)
import Proofs.Local(localInference, locDecomp)
import Proofs.Composition(composition, compositionCreatingEdges)
import Proofs.HideTheoremShift(interactiveHideTheoremShift)
import Proofs.SimpleTheoremHideShift(theoremHideShift)
import Proofs.ComputeColimit(computeColimit)

import Data.IORef
import Data.Graph.Inductive.Graph(lab')
import qualified Data.Map as Map

import Common.DocUtils(showDoc)
import Common.Result as Res
import qualified Common.InjMap as InjMap

import Driver.Options
import Driver.ReadFn(libNameToFile)

import FileDialog(fileDialogStr, newFileDialogStr)
import GraphDisp(emptyArcTypeParms, emptyNodeTypeParms)
import GraphConfigure
import DaVinciGraph
import TextDisplay(createTextDisplay)
import Broadcaster(newSimpleBroadcaster,applySimpleUpdate)
import Sources(toSimpleSource)
import qualified HTk

import Control.Concurrent.MVar

-- | A List of all linktypes and their properties.
linkTypes :: HetcatsOpts
          -> [(String, EdgePattern EdgeValue, String, Bool, Bool)]
linkTypes opts = [
-- Name                   Lineformat             Color       Thm    Other
  ("globaldef",           Solid,                 black,      False, False),
  ("def",                 Solid,                 steelblue,  False, False),
  ("hidingdef",           Solid,                 lightblue,  False, False),
  ("hetdef",              GraphConfigure.Double, black,      False, False),
  ("proventhm",           Solid,                 green,      True,  True),
  ("unproventhm",         Solid,                 coral,      True,  True),
  ("localproventhm",      Dashed,                green,      True,  True),
  ("localunproventhm",    Dashed,                coral,      True,  True),
  ("hetproventhm",        GraphConfigure.Double, green,      True,  True),
  ("hetunproventhm",      GraphConfigure.Double, coral,      True,  True),
  ("hetlocalproventhm",   GraphConfigure.Double, green,      True,  True),
  ("hetlocalunproventhm", GraphConfigure.Double, coral,      True,  True),
  ("unprovenhidingthm",   Solid,                 yellow,     True,  False),
  ("provenhidingthm",     Solid,                 lightgreen, True,  False),
   -- is grey the correct color for reference?
  ("reference",           Dotted,                grey,       False, False)]
  where
    coral = getColor opts "Coral"
    green = getColor opts "Green"
    steelblue = getColor opts "Steelblue"
    lightblue = getColor opts "Lightblue"
    yellow = getColor opts "Yellow"
    lightgreen = getColor opts "Lightgreen"
    grey = getColor opts "Grey"
    black = getColor opts "Black"

-- | A Map of all nodetypes and their properties.
mapLinkTypes :: HetcatsOpts -> Map.Map String (EdgePattern EdgeValue, String)
mapLinkTypes opts = Map.fromList $ map (\(a, b, c, _, _) -> (a, (b,c)))
                                 $ linkTypes opts

-- | A List of all nodetypes and their properties.
nodeTypes :: HetcatsOpts -> [(String, Shape value, String)]
nodeTypes opts = [
-- Name                                   Shape    Color
  ("open_cons__spec",                     Ellipse, coral),
  ("proven_cons__spec",                   Ellipse, coral),
  ("locallyEmpty__open_cons__spec",       Ellipse, coral),
  ("locallyEmpty__proven_cons__spec",     Ellipse, green),
  ("open_cons__internal",                 Ellipse, coral),
  ("proven_cons__internal",               Ellipse, coral),
  ("locallyEmpty__open_cons__internal",   Ellipse, coral),
  ("locallyEmpty__proven_cons__internal", Ellipse, green),
  ("dg_ref",                              Box,     coral),
  ("locallyEmpty__dg_ref",                Box,     green)
  ]
  where
    coral = getColor opts "Coral"
    green = getColor opts "Green"

-- | A Map of all nodetypes and their properties.
mapNodeTypes :: HetcatsOpts -> Map.Map String (Shape value, String)
mapNodeTypes opts = Map.fromList $ map (\(a, b, c) -> (a, (b,c)))
                                 $ nodeTypes opts

-- | A List of CompareTable entries. Hierarchy = Order
compTableEntries :: [String]
compTableEntries = ["globaldef",
                    "def",
                    "hidingdef",
                    "hetdef",
                    "proventhm",
                    "unproventhm",
                    "localproventhm",
                    "localunproventhm",
                    "hetproventhm",
                    "hetunproventhm",
                    "hetlocalproventhm",
                    "hetlocalunproventhm",
                    "unprovenhidingthm",
                    "provenhidingthm",
                    "reference"]

-- | Converts colors to grayscale
getColor :: HetcatsOpts -> String -> String
getColor opts color
  | not $ uncolored opts  = color
  | color == "Coral"      = "darkgrey"
  | color == "Green"      = "lightgrey"
  | color == "Steelblue"  = "steelgrey"
  | color == "Lightblue"  = "lightsteelgrey"
  | color == "Yellow"     = "darksteelgrey"
  | color == "Lightgreen" = "grey"
  | otherwise             = "black"

-- | Creates the graph. Runs makegraph
createGraph :: GInfo -> String -> ConvFunc -> LibFunc -> IO AGV.Result
createGraph gInfo@(GInfo { gi_LIB_NAME = ln
                         , gi_GraphInfo = actGraphInfo
                         , gi_hetcatsOpts = opts
                         }) title convGraph showLib = do
  iorSTEvents <- newIORef (Map.empty::(Map.Map Descr Descr))
  let file = rmSuffix (libNameToFile opts ln) ++ prfSuffix
  makegraphExt title
               (createOpen gInfo file convGraph showLib)
               (createSave gInfo file)
               (createSaveAs gInfo file)
               (createClose gInfo)
               (Just (createExit gInfo))
               (createGlobalMenu gInfo convGraph showLib)
               (createNodeTypes gInfo iorSTEvents convGraph showLib)
               (createLinkTypes gInfo)
               (createCompTable compTableEntries)
               actGraphInfo

-- | Returns the open-function
createOpen :: GInfo -> FilePath -> ConvFunc -> LibFunc -> Maybe (IO ())
createOpen gInfo file convGraph showLib = Just (
  do
    evnt <- fileDialogStr "Open..." file
    maybeFilePath <- HTk.sync evnt
    case maybeFilePath of
      Just filePath -> do
        openProofStatus gInfo filePath convGraph showLib
        return ()
      Nothing -> fail "Could not open file."
  )

-- | Returns the save-function
createSave :: GInfo -> FilePath -> Maybe (IO ())
createSave gInfo file = Just (saveProofStatus gInfo file)

-- | Returns the saveas-function
createSaveAs :: GInfo -> FilePath -> Maybe (IO ())
createSaveAs gInfo file = Just (
  do
    evnt <- newFileDialogStr "Save as..." file
    maybeFilePath <- HTk.sync evnt
    case maybeFilePath of
      Just filePath -> saveProofStatus gInfo filePath
      Nothing -> fail "Could not save file."
  )

-- | Returns the save-function
createClose :: GInfo -> IO Bool
createClose (GInfo { gi_LIB_NAME = ln
                   , libEnvIORef = ioRefProofStatus
                   , windowCount = wc
                   , exitMVar = exit
                   }) = do
  le <- readIORef ioRefProofStatus
  case Map.lookup ln le of
    Just dgraph -> do
      case openlock dgraph of
        Just lock -> do
          notopen <- isEmptyMVar lock
          case notopen of
            True -> error "development graph seems to be closed already"
            False ->  takeMVar lock
        Nothing -> error $ "MVar of " ++ show ln ++ " not initialized"
    Nothing -> error $ "development graph with libname " ++ show ln
                       ++" does not exist"
  count <- takeMVar wc
  case count == 1 of
    True -> putMVar exit ()
    False -> putMVar wc $ count - 1
  return True

-- | Returns the save-function
createExit :: GInfo -> IO ()
createExit (GInfo {exitMVar = exit}) = do
  putMVar exit ()

-- | Creates the global menu
createGlobalMenu :: GInfo -> ConvFunc -> LibFunc -> [GlobalMenu]
createGlobalMenu gInfo@(GInfo { gi_LIB_NAME = ln
                              , gi_hetcatsOpts = opts
                              }) convGraph showLib =
  [GlobalMenu (Menu Nothing
    [ Button "Undo" (runAndLock gInfo (undo gInfo True))
    , Button "Redo" (runAndLock gInfo (undo gInfo False))
    , Button "Reload" (runAndLock gInfo (reload gInfo))
    , Menu (Just "Unnamed nodes")
        [ Button "Hide/show names" (runAndLock gInfo (hideShowNames gInfo True))
        , Button "Hide nodes" (runAndLock gInfo (hideNodes gInfo))
        , Button "Show nodes" (runAndLock gInfo (showNodes gInfo))
      ]
    , Button "Focus node" (focusNode gInfo)
    , Menu (Just "Proofs") $ map ( \ (str, cmd) ->
       Button str (runAndLock gInfo (performProofAction gInfo
         (proofMenu gInfo (return . return . cmd ln))
       )))
       [ ("Automatic", automatic)
       , ("Global Subsumption", globSubsume)
       , ("Global Decomposition", globDecomp)
       , ("Local Inference", localInference)
       , ("Local Decomposition (merge of rules)", locDecomp)
       , ("Composition (merge of rules)", composition)
       , ("Composition - creating new links", compositionCreatingEdges)
       , ("Theorem Hide Shift", theoremHideShift)
       , ("Compute Colimit", computeColimit)
       ] ++
       [Button "Hide Theorem Shift" (runAndLock gInfo (performProofAction gInfo
          (proofMenu gInfo (fmap return . interactiveHideTheoremShift ln))))
       ]
    , Button "Translate Graph" (translateGraph gInfo convGraph showLib)
    , Button "Show Logic Graph" (showLogicGraph daVinciSort)
    , Button "Show Library Graph" (showLibGraph gInfo showLib)
    , Button "Save Graph for uDrawGraph" (saveUDGraph gInfo (mapNodeTypes opts)
                                                      $ mapLinkTypes opts)
    ])
  ]

-- | A list of all Node Types
createNodeTypes :: GInfo -> IORef (Map.Map Descr Descr) -> ConvFunc -> LibFunc
                -> [(String,DaVinciNodeTypeParms (String,Descr,Descr))]
createNodeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) iorSTEvents convGraph
  showLib =
  [("open_cons__spec", createLocalMenuNodeTypeSpec coral iorSTEvents gInfo),
   ("proven_cons__spec", createLocalMenuNodeTypeSpec coral iorSTEvents gInfo),
   ("locallyEmpty__open_cons__spec",
     createLocalMenuNodeTypeSpec coral iorSTEvents gInfo),
   ("locallyEmpty__proven_cons__spec",
     createLocalMenuNodeTypeSpec green iorSTEvents gInfo),
   ("open_cons__internal", createLocalMenuNodeTypeInternal coral gInfo),
   ("proven_cons__internal", createLocalMenuNodeTypeInternal coral gInfo),
   ("locallyEmpty__open_cons__internal",
     createLocalMenuNodeTypeInternal coral gInfo),
   ("locallyEmpty__proven_cons__internal",
     createLocalMenuNodeTypeInternal green gInfo),
   ("dg_ref", createLocalMenuNodeTypeDgRef coral gInfo convGraph showLib),
   ("locallyEmpty__dg_ref",
     createLocalMenuNodeTypeDgRef green gInfo convGraph showLib)
  ]
  where
    coral = getColor opts "Coral"
    green = getColor opts "Green"

-- | the link types (share strings to avoid typos)
createLinkTypes :: GInfo -> [(String,DaVinciArcTypeParms EdgeValue)]
createLinkTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) =
  map (\(title, look, color, thm, extra) ->
        (title, look
            $$$ Color color
            $$$ (if thm then createLocalEdgeMenuThmEdge gInfo
                  else createLocalEdgeMenu gInfo)
            $$$ (if extra then createLocalMenuValueTitleShowConservativity
                  $$$ emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue
                  else
                    emptyArcTypeParms :: DaVinciArcTypeParms EdgeValue))
      ) $ linkTypes opts

-- | Generates the CompTable
createCompTable :: [String] -> CompTable
createCompTable ls =
  concat $ map (\ x -> makeComp x ls False ) ls
  where
    makeComp :: String -> [String] -> Bool -> CompTable
    makeComp _ [] _ = []
    makeComp s (xs:r) b = case b of
      True -> (s, xs, xs) : makeComp s r b
      False -> (s, xs, s) : makeComp s r (s == xs)

-- -------------------------------------------------------------
-- methods to create the local menus of the different nodetypes
-- -------------------------------------------------------------

type NodeDescr = (String, Descr, Descr)

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec :: String -> IORef (Map.Map Descr Descr) -> GInfo
                            -> DaVinciNodeTypeParms NodeDescr
createLocalMenuNodeTypeSpec color ioRefSubtreeEvents gInfo =
                 Ellipse $$$ Color color
                 $$$ ValueTitle (\ (s,_,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSignature gInfo,
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
                                     gInfo,
                    createLocalMenuButtonUndoShowJustSubtree
                                     ioRefSubtreeEvents gInfo,
                    createLocalMenuButtonShowNumberOfNode
                   ])
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
createLocalMenuNodeTypeDgRef :: String -> GInfo -> ConvFunc -> LibFunc
                             -> DaVinciNodeTypeParms NodeDescr
createLocalMenuNodeTypeDgRef color gInfo
  convGraph showLib =
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
                     (\ (_, descr, _) -> do
                       showReferencedLibrary descr gInfo convGraph showLib
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
  createMenuButton "Prove" (\descr dgMap dgraph -> performProofAction gInfo
    (proveAtNode False gInfo descr dgMap dgraph)) gInfo

createLocalMenuButtonCCCAtNode :: GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (proveAtNode True gInfo) gInfo

createLocalMenuButtonShowJustSubtree :: IORef (Map.Map Descr Descr)
                                     -> GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonShowJustSubtree ioRefSubtreeEvents
    gInfo@(GInfo {visibleNodesIORef = ioRefVisibleNodes,
                  gi_GraphInfo = actGraphInfo}) =
                    (Button "Show just subtree"
                      (\ (_, descr, gid) ->
                        do subtreeEvents <- readIORef ioRefSubtreeEvents
                           case Map.lookup descr subtreeEvents of
                             Just _ -> putStrLn $
                               "it is already just the subtree of node "
                                ++  show descr ++" shown"
                             Nothing ->
                               do (eventDescr, newVisibleNodes, errorMsg) <-
                                     showJustSubtree descr gid gInfo
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


createLocalMenuButtonUndoShowJustSubtree :: IORef (Map.Map Descr Descr)
                                         -> GInfo -> ButtonMenu NodeDescr
createLocalMenuButtonUndoShowJustSubtree ioRefSubtreeEvents
    (GInfo {visibleNodesIORef = ioRefVisibleNodes,
            gi_GraphInfo = actGraphInfo}) =
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

getNumberOfRefNode :: Descr -> DGraphAndAGraphNode -> DGraph -> IO ()
getNumberOfRefNode descr dgAndabstrNodeMap dgraph =
  case InjMap.lookupWithB descr dgAndabstrNodeMap of
    Just (_, node) ->
      let dgnode = lab' (contextDG dgraph node)
          title = "Number of node"
       in createTextDisplay title (show (dgn_node dgnode)) [HTk.size(10,10)]
    Nothing -> nodeErr descr

-- -------------------------------------------------------------
-- methods to create the local menus for the edges
-- -------------------------------------------------------------

createLocalEdgeMenu :: GInfo -> LocalMenu EdgeValue
createLocalEdgeMenu gInfo =
    LocalMenu (Menu (Just "edge menu")
               [createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo,
                createLocalMenuButtonShowIDOfEdge gInfo]
              )

createLocalEdgeMenuThmEdge :: GInfo -> LocalMenu EdgeValue
createLocalEdgeMenuThmEdge gInfo =
   LocalMenu (Menu (Just "thm egde menu")
              [ createLocalMenuButtonShowMorphismOfEdge gInfo,
                createLocalMenuButtonShowOriginOfEdge gInfo,
                createLocalMenuButtonShowProofStatusOfThm gInfo,
                createLocalMenuButtonCheckconservativityOfEdge gInfo,
                createLocalMenuButtonShowIDOfEdge gInfo]
              )

createLocalMenuButtonShowMorphismOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowMorphismOfEdge _ = Button "Show morphism"
    ( \ (_, descr, maybeLEdge)  -> showMorphismOfEdge descr maybeLEdge)

createLocalMenuButtonShowOriginOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowOriginOfEdge _ = Button "Show origin"
    ( \ (_, descr, maybeLEdge) -> showOriginOfEdge descr maybeLEdge)

createLocalMenuButtonCheckconservativityOfEdge :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonCheckconservativityOfEdge gInfo =
    Button "Check conservativity (preliminary)"
    ( \ (_, descr, maybeLEdge)  ->
        checkconservativityOfEdge descr gInfo maybeLEdge)

createLocalMenuButtonShowProofStatusOfThm :: GInfo -> ButtonMenu EdgeValue
createLocalMenuButtonShowProofStatusOfThm _ = Button "Show proof status"
    ( \ (_, descr, maybeLEdge) -> showProofStatusOfThm descr maybeLEdge)

createLocalMenuValueTitleShowConservativity :: ValueTitle EdgeValue
createLocalMenuValueTitleShowConservativity = ValueTitle
      ( \ (_, _, maybeLEdge) ->
        case maybeLEdge of
          Just (_,_,edgelab) ->
            case dgl_type edgelab of
                        GlobalThm _ c status -> return (showCons c status)
                        LocalThm _ c status -> return (showCons c status)
                        _ -> return ""
          Nothing -> return "")
  where
    showCons :: Conservativity -> ThmLinkStatus -> String
    showCons c status =
      case (c, status) of
        (None, _) -> show c
        (_, LeftOpen) -> (show c) ++ "?"
        _ -> show c

-- ------------------------------
-- end of local menu definitions
-- ------------------------------
