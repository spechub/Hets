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

import qualified GUI.GraphAbstraction as GA
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
          -> [(String, EdgePattern GA.EdgeValue, String, Bool, Bool)]
linkTypes opts = [
-- Name                      Lineformat             Color       Thm    Other
  ("globaldef",              Solid,                 black,      False, False),
  ("globaldefInc",           Solid,                 black,      False, False),
  ("localdef",               Dashed,                black,      False, False),
  ("localdefInc",            Dashed,                black,      False, False),
  ("def",                    Solid,                 steelblue,  False, False),
  ("defInc",                 Solid,                 steelblue,  False, False),
  ("hidingdef",              Solid,                 lightblue,  False, False),
  ("hidingdefInc",           Solid,                 lightblue,  False, False),
  ("hetdef",                 GraphConfigure.Double, black,      False, False),
  ("hetdefInc",              GraphConfigure.Double, black,      False, False),
  ("proventhm",              Solid,                 green,      True,  True),
  ("proventhmInc",           Solid,                 green,      True,  True),
  ("unproventhm",            Solid,                 coral,      True,  True),
  ("unproventhmInc",         Solid,                 coral,      True,  True),
  ("localproventhm",         Dashed,                green,      True,  True),
  ("localproventhmInc",      Dashed,                green,      True,  True),
  ("localunproventhm",       Dashed,                coral,      True,  True),
  ("localunproventhmInc",    Dashed,                coral,      True,  True),
  ("hetproventhm",           GraphConfigure.Double, green,      True,  True),
  ("hetproventhmInc",        GraphConfigure.Double, green,      True,  True),
  ("hetunproventhm",         GraphConfigure.Double, coral,      True,  True),
  ("hetunproventhmInc",      GraphConfigure.Double, coral,      True,  True),
  ("hetlocalproventhm",      GraphConfigure.Double, green,      True,  True),
  ("hetlocalproventhmInc",   GraphConfigure.Double, green,      True,  True),
  ("hetlocalunproventhm",    GraphConfigure.Double, coral,      True,  True),
  ("hetlocalunproventhmInc", GraphConfigure.Double, coral,      True,  True),
  ("unprovenhidingthm",      Solid,                 yellow,     True,  False),
  ("unprovenhidingthmInc",   Solid,                 yellow,     True,  False),
  ("provenhidingthm",        Solid,                 lightgreen, True,  False),
  ("provenhidingthmInc",     Solid,                 lightgreen, True,  False),
  ("reference",              Dotted,                grey,       False, False),
  ("referenceInc",           Dotted,                grey,       False, False)]
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
mapLinkTypes :: HetcatsOpts -> Map.Map String (EdgePattern GA.EdgeValue, String)
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
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(String,DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) convGraph showLib =
  [("open_cons__spec", createLocalMenuNodeTypeSpec coral gInfo),
   ("proven_cons__spec", createLocalMenuNodeTypeSpec coral gInfo),
   ("locallyEmpty__open_cons__spec", createLocalMenuNodeTypeSpec coral gInfo),
   ("locallyEmpty__proven_cons__spec", createLocalMenuNodeTypeSpec green gInfo),
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
createLinkTypes :: GInfo -> [(String,DaVinciArcTypeParms GA.EdgeValue)]
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

-- -------------------------------------------------------------
-- methods to create the local menus of the different nodetypes
-- -------------------------------------------------------------

-- | local menu for the nodetypes spec and locallyEmpty_spec
createLocalMenuNodeTypeSpec :: String -> GInfo
                            -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeSpec color gInfo =
                 Ellipse $$$ Color color
                 $$$ ValueTitle (\ (s,_) -> return s)
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
                    createLocalMenuButtonShowNumberOfNode gInfo
                   ])
                  $$$ emptyNodeTypeParms

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
                 $$$ LocalMenu (Menu (Just "node menu")
                    [createLocalMenuButtonShowSpec gInfo,
                     createLocalMenuButtonShowNumberOfNode gInfo,
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
                             -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNodeTypeDgRef color gInfo convGraph showLib =
                 Box $$$ Color color
                 $$$ ValueTitle (\ (s,_) -> return s)
                 $$$ LocalMenu (Menu (Just "node menu")
                   [createLocalMenuButtonShowSignature gInfo,
                    createLocalMenuButtonShowTheory gInfo,
                    createLocalMenuButtonProveAtNode gInfo,
                    createLocalMenuButtonShowProofStatusOfNode gInfo,
                    createLocalMenuButtonShowNumberOfNode gInfo,
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

createLocalMenuButtonShowSignature :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowSignature =
  createMenuButton "Show signature" getSignatureOfNode

createLocalMenuButtonShowTheory :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowTheory gInfo =
  createMenuButton "Show theory" (getTheoryOfNode gInfo) gInfo

createLocalMenuButtonShowLocalAx :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowLocalAx gInfo =
  createMenuButton "Show local axioms" getLocalAxOfNode gInfo

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
               Res.Result [] (Just (n, gth)) -> displayFun (showDoc n "") gth
               Res.Result ds _ -> showDiags defaultHetcatsOpts ds

createLocalMenuButtonShowSublogic :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowSublogic gInfo@(GInfo { gi_LIB_NAME = ln
                                               , libEnvIORef = le }) =
  createMenuButton "Show sublogic" (getSublogicOfNode le ln) gInfo

createLocalMenuButtonShowNodeOrigin :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowNodeOrigin  =
  createMenuButton "Show origin" showOriginOfNode

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

createLocalMenuButtonShowNumberOfNode :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowNumberOfNode gInfo =
  createMenuButton "Show number of node" getIdOfNode gInfo

-- -------------------------------------------------------------
-- methods to create the local menus for the edges
-- -------------------------------------------------------------

createLocalEdgeMenu :: GInfo -> LocalMenu GA.EdgeValue
createLocalEdgeMenu gInfo =
  LocalMenu (Menu (Just "edge menu")
                  [ createLocalMenuButtonShowMorphismOfEdge gInfo
                  , createLocalMenuButtonShowOriginOfEdge gInfo
                  , createLocalMenuButtonCheckconservativityOfEdge gInfo
                  , createLocalMenuButtonShowIDOfEdge gInfo])

createLocalEdgeMenuThmEdge :: GInfo -> LocalMenu GA.EdgeValue
createLocalEdgeMenuThmEdge gInfo =
  LocalMenu (Menu (Just "thm egde menu")
                  [ createLocalMenuButtonShowMorphismOfEdge gInfo
                  , createLocalMenuButtonShowOriginOfEdge gInfo
                  , createLocalMenuButtonShowProofStatusOfThm gInfo
                  , createLocalMenuButtonCheckconservativityOfEdge gInfo
                  , createLocalMenuButtonShowIDOfEdge gInfo])

createLocalMenuButtonShowMorphismOfEdge :: GInfo -> ButtonMenu GA.EdgeValue
createLocalMenuButtonShowMorphismOfEdge _ = Button "Show morphism"
  (\ (_, (EdgeId descr), maybeLEdge)  -> showMorphismOfEdge descr maybeLEdge)

createLocalMenuButtonShowOriginOfEdge :: GInfo -> ButtonMenu GA.EdgeValue
createLocalMenuButtonShowOriginOfEdge _ = Button "Show origin"
  (\ (_, (EdgeId descr), maybeLEdge) -> showOriginOfEdge descr maybeLEdge)

createLocalMenuButtonCheckconservativityOfEdge :: GInfo
                                               -> ButtonMenu GA.EdgeValue
createLocalMenuButtonCheckconservativityOfEdge gInfo =
  Button "Check conservativity (preliminary)"
    (\ (_, (EdgeId descr), maybeLEdge)  ->
      checkconservativityOfEdge descr gInfo maybeLEdge)

createLocalMenuButtonShowProofStatusOfThm :: GInfo -> ButtonMenu GA.EdgeValue
createLocalMenuButtonShowProofStatusOfThm _ = Button "Show proof status"
  (\ (_, (EdgeId descr), maybeLEdge) -> showProofStatusOfThm descr maybeLEdge)

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

-- | for debugging
createLocalMenuButtonShowIDOfEdge :: GInfo -> ButtonMenu GA.EdgeValue
createLocalMenuButtonShowIDOfEdge _ =
  (Button "Show ID of this edge" (\ (_, (EdgeId descr),maybeLEdge) -> do
                                   showIDOfEdge descr maybeLEdge
                                   return ()))

-- ------------------------------
-- end of local menu definitions
-- ------------------------------
