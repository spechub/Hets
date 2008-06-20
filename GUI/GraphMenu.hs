{- |
Module      :  $Header$
Description :  Menu creation functions for the Graphdisplay
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2002-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Menu creation
-}

module GUI.GraphMenu (createGraph) where

import qualified GUI.GraphAbstraction as GA
import GUI.GraphTypes
import GUI.GraphLogic
import GUI.ShowLogicGraph(showLogicGraph)

import Static.DevGraph
import Static.DGFlattening

import Proofs.Automatic(automatic)
import Proofs.Global(globSubsume, globDecomp)
import Proofs.Local(localInference, locDecomp)
import Proofs.Composition(composition, compositionCreatingEdges)
import Proofs.HideTheoremShift(interactiveHideTheoremShift)
import Proofs.TheoremHideShift(theoremHideShift)
import Proofs.ComputeColimit(computeColimit)

import Data.IORef
import qualified Data.Map as Map

import Common.DocUtils(showDoc)
import Common.Result as Res

import Driver.Options
import Driver.ReadFn(libNameToFile)

import FileDialog(fileDialogStr, newFileDialogStr)
import GraphDisp(emptyArcTypeParms, emptyNodeTypeParms)
import GraphConfigure
import DaVinciGraph
import Broadcaster(newSimpleBroadcaster,applySimpleUpdate)
import Sources(toSimpleSource)
import qualified HTk

import Control.Concurrent.MVar

-- | A List of all linktypes and their properties. Hierarchy = Order
linkTypes :: HetcatsOpts
          -> [(DGEdgeType, EdgePattern GA.EdgeValue, String, Bool, Bool)]
linkTypes opts = [
-- Name                      Lineformat             Color       Thm    Other
  (GlobalDefNoInc,           Solid,                 black,      False, False),
  (GlobalDefInc,             Solid,                 black,      False, False),
  (LocalDefNoInc,            Dashed,                black,      False, False),
  (LocalDefInc,              Dashed,                black,      False, False),
  (DefNoInc,                 Solid,                 steelblue,  False, False),
  (DefInc,                   Solid,                 steelblue,  False, False),
  (HidingDefNoInc,           Solid,                 lightblue,  False, False),
  (HidingDefInc,             Solid,                 lightblue,  False, False),
  (HetDefNoInc,              GraphConfigure.Double, black,      False, False),
  (HetDefInc,                GraphConfigure.Double, black,      False, False),
  (ProvenThmNoInc,           Solid,                 green,      True,  True),
  (ProvenThmInc,             Solid,                 green,      True,  True),
  (UnprovenThmNoInc,         Solid,                 coral,      True,  True),
  (UnprovenThmInc,           Solid,                 coral,      True,  True),
  (LocalProvenThmNoInc,      Dashed,                green,      True,  True),
  (LocalProvenThmInc,        Dashed,                green,      True,  True),
  (LocalUnprovenThmNoInc,    Dashed,                coral,      True,  True),
  (LocalUnprovenThmInc,      Dashed,                coral,      True,  True),
  (HetProvenThmNoInc,        GraphConfigure.Double, green,      True,  True),
  (HetProvenThmInc,          GraphConfigure.Double, green,      True,  True),
  (HetUnprovenThmNoInc,      GraphConfigure.Double, coral,      True,  True),
  (HetUnprovenThmInc,        GraphConfigure.Double, coral,      True,  True),
  (HetLocalProvenThmNoInc,   GraphConfigure.Double, green,      True,  True),
  (HetLocalProvenThmInc,     GraphConfigure.Double, green,      True,  True),
  (HetLocalUnprovenThmNoInc, GraphConfigure.Double, coral,      True,  True),
  (HetLocalUnprovenThmInc,   GraphConfigure.Double, coral,      True,  True),
  (UnprovenHidingThmNoInc,   Solid,                 yellow,     True,  False),
  (UnprovenHidingThmInc,     Solid,                 yellow,     True,  False),
  (ProvenHidingThmNoInc,     Solid,                 lightgreen, True,  False),
  (ProvenHidingThmInc,       Solid,                 lightgreen, True,  False),
  (ReferenceNoInc,           Dotted,                grey,       False, False),
  (ReferenceInc,             Dotted,                grey,       False, False)]
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
mapLinkTypes :: HetcatsOpts
             -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
mapLinkTypes opts = Map.fromList $ map (\(a, b, c, _, _) -> (a, (b,c)))
                                 $ linkTypes opts


-- | A List of all nodetypes and their properties.
nodeTypes :: HetcatsOpts -> [(DGNodeType, Shape value, String)]
nodeTypes opts = [
-- Name                            Shape    Color
  (NotEmptyOpenConsSpec,           Ellipse, coral),
  (NotEmptyProvenConsSpec,         Ellipse, coral),
  (LocallyEmptyOpenConsSpec,       Ellipse, coral),
  (LocallyEmptyProvenConsSpec,     Ellipse, green),
  (NotEmptyOpenConsInternal,       Ellipse, coral),
  (NotEmptyProvenConsInternal,     Ellipse, coral),
  (LocallyEmptyOpenConsInternal,   Ellipse, coral),
  (LocallyEmptyProvenConsInternal, Ellipse, green),
  (NotEmptyDGRef,                  Box,     coral),
  (LocallyEmptyDGRef,              Box,     green)
  ]
  where
    coral = getColor opts "Coral"
    green = getColor opts "Green"

-- | A Map of all nodetypes and their properties.
mapNodeTypes :: HetcatsOpts -> Map.Map DGNodeType (Shape value, String)
mapNodeTypes opts = Map.fromList $ map (\(a, b, c) -> (a, (b,c)))
                                 $ nodeTypes opts

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
createGraph :: GInfo -> String -> ConvFunc -> LibFunc -> IO ()
createGraph gInfo@(GInfo { gi_LIB_NAME = ln
                         , gi_GraphInfo = actGraphInfo
                         , gi_hetcatsOpts = opts
                         }) title convGraph showLib = do
  let file = rmSuffix (libNameToFile opts ln) ++ prfSuffix
  GA.makegraphExt actGraphInfo
                  title
                  (createOpen gInfo file convGraph showLib)
                  (createSave gInfo file)
                  (createSaveAs gInfo file)
                  (createClose gInfo)
                  (Just (createExit gInfo))
                  (createGlobalMenu gInfo convGraph showLib)
                  (createNodeTypes gInfo convGraph showLib)
                  (createLinkTypes gInfo)

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
  let ral x = runAndLock gInfo x in
  [GlobalMenu (Menu Nothing
    [ Button "Undo" $ ral $ undo gInfo True
    , Button "Redo" $ ral $ undo gInfo False
    , Button "Reload" $ ral $ reload gInfo
    , Menu (Just "Unnamed nodes")
        [ Button "Hide/show names" $ ral $ hideShowNames gInfo True
        , Button "Hide nodes" $ ral $ hideNodes gInfo
        , Button "Show nodes" $ ral $ showNodes gInfo
      ]
    , Button "Focus node" $ ral $ focusNode gInfo
    , Menu (Just "Proofs") $ map ( \ (str, cmd) ->
       Button str $ ral $ performProofAction gInfo
                  $ proofMenu gInfo $ return . return . cmd ln)
       [ ("Automatic", automatic)
       , ("Global Subsumption", globSubsume)
       , ("Global Decomposition", globDecomp)
       , ("Local Inference", localInference)
       , ("Local Decomposition (merge of rules)", locDecomp)
       , ("Composition (merge of rules)", composition)
       , ("Composition - creating new links", compositionCreatingEdges)
       ] ++
       [Button "Hide Theorem Shift" $ ral $ performProofAction gInfo
               $ proofMenu gInfo $ fmap return . interactiveHideTheoremShift ln
       ] ++
       map (\ (str, cmd) ->
              Button str $ ral $ performProofAction gInfo
                  $ proofMenu gInfo $ return . cmd ln)
       [ ("Theorem Hide Shift", theoremHideShift)
       , ("Compute Colimit", computeColimit)
       ] ++
       [Button "Flattening (form 1 to 0)" $ ral $ performProofAction gInfo
                $ proofMenu gInfo $ return . libEnv_flattening1
       ] ++
       [Button "Flattening (form 4 to 0)" $ ral $ performProofAction gInfo
                $ proofMenu gInfo $ return . libEnv_flattening4
       ] ++
       [Button "Flattening (form 5 to 0)" $ ral $ performProofAction gInfo
                $ proofMenu gInfo $ return . libEnv_flattening5
       ] ++
       [Button "Flattening (form 6 to 0)" $ ral $ performProofAction gInfo
                $ proofMenu gInfo $ return . libEnv_flattening6
       ]
    , Button "Translate Graph" $ ral $ translateGraph gInfo convGraph showLib
    , Button "Show Logic Graph" $ ral $ showLogicGraph daVinciSort
    , Button "Show Library Graph" $ ral $ showLibGraph gInfo showLib
    , Button "Save Graph for uDrawGraph" $ ral $ saveUDGraph gInfo (mapNodeTypes opts) $ mapLinkTypes opts
    ])
  ]

-- | A list of all Node Types
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(DGNodeType,DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) cGraph showLib =
  [(NotEmptyOpenConsSpec, createLocalMenuNodeTypeSpec c gInfo),
   (NotEmptyProvenConsSpec, createLocalMenuNodeTypeSpec c gInfo),
   (LocallyEmptyOpenConsSpec, createLocalMenuNodeTypeSpec c gInfo),
   (LocallyEmptyProvenConsSpec, createLocalMenuNodeTypeSpec g gInfo),
   (NotEmptyOpenConsInternal, createLocalMenuNodeTypeInternal c gInfo),
   (NotEmptyProvenConsInternal, createLocalMenuNodeTypeInternal c gInfo),
   (LocallyEmptyOpenConsInternal, createLocalMenuNodeTypeInternal c gInfo),
   (LocallyEmptyProvenConsInternal, createLocalMenuNodeTypeInternal g gInfo),
   (NotEmptyDGRef, createLocalMenuNodeTypeDgRef c gInfo cGraph showLib),
   (LocallyEmptyDGRef, createLocalMenuNodeTypeDgRef g gInfo cGraph showLib)]
  where
    c = getColor opts "Coral"
    g = getColor opts "Green"

-- | the link types (share strings to avoid typos)
createLinkTypes :: GInfo -> [(DGEdgeType,DaVinciArcTypeParms GA.EdgeValue)]
createLinkTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) =
  map (\(title, look, color, thm, extra) ->
        (title, look
            $$$ Color color
            $$$ (if thm then createLocalEdgeMenuThmEdge gInfo
                  else createLocalEdgeMenu gInfo)
            $$$ (if extra then createLocalMenuValueTitleShowConservativity
                  $$$ emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue
                  else
                    emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue))
      ) $ linkTypes opts

-- * methods to create the local menus of the different nodetypes

createLocalMenuNode :: GInfo -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNode gInfo = LocalMenu (Menu (Just "node menu") $ map ($ gInfo)
  [ createLocalMenuButtonShowNodeInfo
  , createLocalMenuButtonShowTheory
  , createLocalMenuButtonTranslateTheory
  , createLocalMenuTaxonomy
  , createLocalMenuButtonShowSpec
  , createLocalMenuButtonShowProofStatusOfNode
  , createLocalMenuButtonProveAtNode
  , createLocalMenuButtonCCCAtNode ]) $$$ emptyNodeTypeParms

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec :: String -> GInfo
                            -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeSpec color gInfo =
                 Ellipse $$$ Color color
                 $$$ ValueTitle (\ (s,_) -> return s)
                 $$$ createLocalMenuNode gInfo

-- | local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal :: String -> GInfo
                                -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeInternal color
               gInfo@(GInfo {internalNamesIORef = showInternalNames}) =
                 Ellipse $$$ Color color
                 $$$ ValueTitleSource (\ (s,_) -> do
                       b <- newSimpleBroadcaster ""
                       intrn <- readIORef showInternalNames
                       let upd = (s,applySimpleUpdate b)
                       writeIORef showInternalNames
                                  $ intrn {updater = upd:updater intrn}
                       return $ toSimpleSource b)
                 $$$ createLocalMenuNode gInfo

-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef :: String -> GInfo -> ConvFunc -> LibFunc
                             -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeDgRef color gInfo convGraph showLib =
                 Box $$$ Color color
                 $$$ ValueTitle (\ (s,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowNodeInfo gInfo,
                    createLocalMenuButtonShowTheory gInfo,
                    createLocalMenuButtonShowProofStatusOfNode gInfo,
                    createLocalMenuButtonProveAtNode gInfo,
                    Button "Show referenced library"
                     (\ (_, descr) -> do
                       showReferencedLibrary descr gInfo convGraph showLib
                       return ()
                     )])
                 $$$ emptyNodeTypeParms

type ButtonMenu a = MenuPrim (Maybe String) (a -> IO ())

-- | menu button for local menus
createMenuButton :: String -> (Int -> DGraph -> IO ())
                 -> GInfo -> ButtonMenu GA.NodeValue
createMenuButton title menuFun gInfo =
                    (Button title
                      (\ (_, descr) ->
                        do le <- readIORef $ libEnvIORef gInfo
                           let dGraph = lookupDGraph (gi_LIB_NAME gInfo) le
                           menuFun descr dGraph
                           return ()
                       )
                    )

createLocalMenuButtonShowSpec :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowSpec = createMenuButton "Show spec" showSpec

createLocalMenuButtonShowTheory :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowTheory gInfo =
  createMenuButton "Show theory" (getTheoryOfNode gInfo) gInfo

createLocalMenuButtonTranslateTheory :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonTranslateTheory gInfo =
  createMenuButton "Translate theory" (translateTheoryOfNode gInfo) gInfo

{- |
   create a sub Menu for taxonomy visualisation
   (added by KL)
-}
createLocalMenuTaxonomy :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuTaxonomy ginfo@(GInfo { gi_LIB_NAME = ln
                                     , libEnvIORef = le }) =
  (Menu (Just "Taxonomy graphs")
        [ createMenuButton "Subsort graph" (passTh displaySubsortGraph) ginfo
        , createMenuButton "Concept graph" (passTh displayConceptGraph) ginfo
        ])
  where passTh displayFun descr _ =
          do r <- lookupTheoryOfNode le ln descr
             case r of
               Res.Result [] (Just (_le',n, gth)) ->
                  displayFun (showDoc n "") gth
          -- le is the changed LibEnv, have to modify
               Res.Result ds _ -> showDiags defaultHetcatsOpts ds

createLocalMenuButtonShowProofStatusOfNode :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowProofStatusOfNode gInfo =
  createMenuButton "Show proof status" (showProofStatusOfNode gInfo) gInfo

createLocalMenuButtonProveAtNode :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonProveAtNode gInfo =
  createMenuButton "Prove" (\descr dgraph -> performProofAction gInfo
    (proveAtNode False gInfo descr dgraph)) gInfo

createLocalMenuButtonCCCAtNode :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (proveAtNode True gInfo) gInfo

createLocalMenuButtonShowNodeInfo :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowNodeInfo gInfo =
  createMenuButton "Show node info" showNodeInfo gInfo

-- * methods to create the local menus for the edges

createLocalEdgeMenu :: GInfo -> LocalMenu GA.EdgeValue
createLocalEdgeMenu gInfo =
  LocalMenu (Menu (Just "edge menu")
                  [ createLocalMenuButtonShowEdgeInfo gInfo
                  , createLocalMenuButtonCheckconservativityOfEdge gInfo])

createLocalEdgeMenuThmEdge :: GInfo -> LocalMenu GA.EdgeValue
createLocalEdgeMenuThmEdge gInfo =
  LocalMenu (Menu (Just "thm egde menu")
                  [ createLocalMenuButtonShowEdgeInfo gInfo
                  , createLocalMenuButtonCheckconservativityOfEdge gInfo])

createLocalMenuButtonShowEdgeInfo :: GInfo -> ButtonMenu GA.EdgeValue
createLocalMenuButtonShowEdgeInfo _ = Button "Show info"
  (\ (_, (EdgeId descr), maybeLEdge) -> showEdgeInfo descr maybeLEdge)

createLocalMenuButtonCheckconservativityOfEdge :: GInfo
                                               -> ButtonMenu GA.EdgeValue
createLocalMenuButtonCheckconservativityOfEdge gInfo =
  Button "Check conservativity (preliminary)"
    (\ (_, (EdgeId descr), maybeLEdge)  ->
      checkconservativityOfEdge descr gInfo maybeLEdge)

createLocalMenuValueTitleShowConservativity :: ValueTitle GA.EdgeValue
createLocalMenuValueTitleShowConservativity = ValueTitle
  (\ (_, _, maybeLEdge) -> case maybeLEdge of
    Just (_,_,edgelab) -> case dgl_type edgelab of
      GlobalThm _ c status -> return (showCons c status)
      LocalThm _ c status -> return (showCons c status)
      _ -> return ""
    Nothing -> return "")
  where
    showCons :: Conservativity -> ThmLinkStatus -> String
    showCons c status = case (c, status) of
      (None, _) -> ""
      (_, LeftOpen) -> show c ++ "?"
      _ -> show c
