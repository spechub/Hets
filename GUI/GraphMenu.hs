{-# OPTIONS -cpp #-}
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

module GUI.GraphMenu
  ( createGraph )
  where

import qualified GUI.GraphAbstraction as GA
import GUI.GraphTypes
import GUI.GraphLogic
import GUI.ShowLogicGraph(showLogicGraph)
import GUI.History
#ifdef GTKGLADE
import GUI.GtkLinkTypeChoice
import Data.List (isSuffixOf)
import Data.Char (toLower)
#endif

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
-- Name                      Lineformat Color      Thm    Other
  (GlobalDefNoInc,           Solid,     blackB c,  False, False),
  (GlobalDefInc,             Solid,     blackD c,  False, False),
  (LocalDefNoInc,            Dashed,    blackB c,  False, False),
  (LocalDefInc,              Dashed,    blackD c,  False, False),
  (DefNoInc,                 Solid,     blue1B c,  False, False),
  (DefInc,                   Solid,     blue1D c,  False, False),
  (HidingDefNoInc,           Solid,     blue2B c,  False, False),
  (HidingDefInc,             Solid,     blue2D c,  False, False),
  (HetDefNoInc,              Double,    blackB c,  False, False),
  (HetDefInc,                Double,    blackD c,  False, False),
  (ProvenThmNoInc,           Solid,     green1B c, True,  True),
  (ProvenThmInc,             Solid,     green1D c, True,  True),
  (UnprovenThmNoInc,         Solid,     coral1B c, True,  True),
  (UnprovenThmInc,           Solid,     coral1D c, True,  True),
  (LocalProvenThmNoInc,      Dashed,    green1B c, True,  True),
  (LocalProvenThmInc,        Dashed,    green1D c, True,  True),
  (LocalUnprovenThmNoInc,    Dashed,    coral1B c, True,  True),
  (LocalUnprovenThmInc,      Dashed,    coral1D c, True,  True),
  (HetProvenThmNoInc,        Double,    green1B c, True,  True),
  (HetProvenThmInc,          Double,    green1D c, True,  True),
  (HetUnprovenThmNoInc,      Double,    coral1B c, True,  True),
  (HetUnprovenThmInc,        Double,    coral1D c, True,  True),
  (HetLocalProvenThmNoInc,   Double,    green2B c, True,  True),
  (HetLocalProvenThmInc,     Double,    green2D c, True,  True),
  (HetLocalUnprovenThmNoInc, Double,    coral2B c, True,  True),
  (HetLocalUnprovenThmInc,   Double,    coral2D c, True,  True),
  (UnprovenHidingThmNoInc,   Solid,     yellowB c, True,  False),
  (UnprovenHidingThmInc,     Solid,     yellowD c, True,  False),
  (ProvenHidingThmNoInc,     Solid,     green2B c, True,  False),
  (ProvenHidingThmInc,       Solid,     green2D c, True,  False),
  (ReferenceNoInc,           Dotted,    khakiB c,  False, False),
  (ReferenceInc,             Dotted,    khakiD c,  False, False)]
  where
    c = colors opts

-- | A Map of all nodetypes and their properties.
mapLinkTypes :: HetcatsOpts
             -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
mapLinkTypes opts = Map.fromList $ map (\(a, b, c, _, _) -> (a, (b,c)))
                                 $ linkTypes opts

#ifdef GTKGLADE
mapLinkTypesToNames :: HetcatsOpts -> [String]
mapLinkTypesToNames = map (\ s -> map toLower $ take (length s - 5) s)
  . filter (isSuffixOf "NoInc")
  . map (\ (a, _, _, _, _) -> show a) . linkTypes
#endif

-- | A List of all nodetypes and their properties.
nodeTypes :: HetcatsOpts -> [(DGNodeType, String, Shape GA.NodeValue, String)]
nodeTypes opts = [
-- Name                            Type        Shape    Color
  (NotEmptyOpenConsSpec,           "Spec",     Ellipse, coral1D c),
  (NotEmptyProvenConsSpec,         "Spec",     Ellipse, coral1B c),
  (LocallyEmptyOpenConsSpec,       "Spec",     Ellipse, coral2D c),
  (LocallyEmptyProvenConsSpec,     "Spec",     Ellipse, green2B c),
  (NotEmptyOpenConsInternal,       "Internal", Circle,  coral1D c),
  (NotEmptyProvenConsInternal,     "Internal", Circle,  coral1B c),
  (LocallyEmptyOpenConsInternal,   "Internal", Circle,  coral2D c),
  (LocallyEmptyProvenConsInternal, "Internal", Circle,  green2B c),
  (NotEmptyDGRef,                  "Ref",      Box,     coral1D c),
  (LocallyEmptyDGRef,              "Ref",      Box,     green2D c)]
  where
    c = colors opts

-- | A Map of all nodetypes and their properties.
mapNodeTypes :: HetcatsOpts -> Map.Map DGNodeType (Shape GA.NodeValue, String)
mapNodeTypes opts = Map.fromList $ map (\(a, _, b, c) -> (a, (b,c)))
                                 $ nodeTypes opts

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
                              , commandHist = ch
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
#ifdef GTKGLADE
    , Button "Select Linktypes" (showLinkTypeChoiceDialog
                                   (mapLinkTypesToNames opts)
                                   print)
#endif
    , Menu (Just "Proofs") $ map ( \ (str, cmd) ->
       Button str $ ral $ performProofAction gInfo
                  $ proofMenu gInfo $ return . return . cmd ln)
       [ ("Automatic",
                         addToHistUnsafe ch "dg-all auto" automatic)
       , ("Global Subsumption",
                         addToHistUnsafe ch "dg-all glob-subsume" globSubsume)
       , ("Global Decomposition",
                         addToHistUnsafe ch "dg-all glob-decomp" globDecomp)
       , ("Local Inference",
                         addToHistUnsafe ch "dg-all loc-infer" localInference)
       , ("Local Decomposition (merge of rules)",
                         addToHistUnsafe ch "dg-all loc-decomp" locDecomp)
       , ("Composition (merge of rules)",
                         addToHistUnsafe ch "dg-all comp" composition)
       , ("Composition - creating new links",
                         addToHistUnsafe ch "dg-all comp-new" compositionCreatingEdges)
       ] ++
       [Button "Hide Theorem Shift" $ addToHistUnsafe ch "dg-all hide-thm"
               $ ral $ performProofAction gInfo
               $ proofMenu gInfo $ fmap return . interactiveHideTheoremShift ln
       ] ++
       map (\ (str, cmd) ->
              Button str $ ral $ performProofAction gInfo
                  $ proofMenu gInfo $ return . cmd ln)
       [ ("Theorem Hide Shift",
                         addToHistUnsafe ch "dg-all thm-hide" theoremHideShift)
       , ("Compute Colimit", computeColimit)
       ] ++
       [ Menu (Just "Flattening") $ map ( \ (str, cmd) ->
          Button str $ ral $ performProofAction gInfo
                     $ proofMenu gInfo $ return . cmd)
             [ ("Importings", libEnv_flattening2)
             , ("Disjoint unions", libEnv_flattening3)
             , ("Importings and renamings", libEnv_flattening4)
             , ("Hiding", libEnv_flattening5)
             , ("Heterogeneity", libEnv_flattening6)]]
    , Button "Translate Graph" $ ral $ translateGraph gInfo convGraph showLib
    , Button "Show Logic Graph" $ ral $ showLogicGraph daVinciSort
    , Button "Show Library Graph" $ ral $ showLibGraph gInfo showLib
    , Button "Save Graph for uDrawGraph" $ ral
             $ saveUDGraph gInfo (mapNodeTypes opts) $ mapLinkTypes opts
    , Button "Save proof-script" $ ral $ askSaveProofScript gInfo
    ])
  ]

-- | Displays a Save-As dialog and writes the proof-script.
askSaveProofScript :: GInfo -> IO ()
askSaveProofScript (GInfo { commandHist = ch }) =
  do
    file <- getProofScriptFileName ch
    evnt <- newFileDialogStr "Save as..." file
    maybeFilePath <- HTk.sync evnt
    case maybeFilePath of
      Just filePath -> saveCommandHistory ch filePath
      Nothing -> fail "Could not save file."

-- | A list of all Node Types
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(DGNodeType,DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) cGraph showLib =
  map (\ (n, t, s, c) -> (n, menu t s c)) $ nodeTypes opts
  where
    menu t s c =
      case t of
        "Spec" -> createLocalMenuNodeTypeSpec s c gInfo
        "Internal" -> createLocalMenuNodeTypeInternal s c gInfo
        "Ref" -> createLocalMenuNodeTypeDgRef s c gInfo cGraph showLib
        _ -> error "CreateNodeTypes: Error in nodeTypes table: Type not known."

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
  , createLocalMenuButtonShowProofStatusOfNode
  , createLocalMenuButtonProveAtNode
  , createLocalMenuButtonCCCAtNode ]) $$$ emptyNodeTypeParms

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec :: Shape GA.NodeValue -> String -> GInfo
                            -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeSpec shape color gInfo =
                 shape $$$ Color color
                 $$$ ValueTitle (\ (s,_) -> return s)
                 $$$ createLocalMenuNode gInfo

-- | local menu for the nodetypes internal and locallyEmpty_internal
createLocalMenuNodeTypeInternal :: Shape GA.NodeValue -> String -> GInfo
                                -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeInternal shape color
               gInfo@(GInfo {internalNamesIORef = showInternalNames}) =
                 shape $$$ Color color
                 $$$ ValueTitleSource (\ (s,_) -> do
                       b <- newSimpleBroadcaster ""
                       intrn <- readIORef showInternalNames
                       let upd = (s,applySimpleUpdate b)
                       writeIORef showInternalNames
                                  $ intrn {updater = upd:updater intrn}
                       return $ toSimpleSource b)
                 $$$ createLocalMenuNode gInfo

-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createLocalMenuNodeTypeDgRef :: Shape GA.NodeValue -> String -> GInfo
                             -> ConvFunc -> LibFunc
                             -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeDgRef shape color gInfo convGraph showLib =
                 shape $$$ Color color
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
