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
import GUI.Utils
#ifdef GTKGLADE
import GUI.GtkLinkTypeChoice
import GUI.GtkConsistencyChecker
#endif

import Data.IORef
import qualified Data.Map as Map
import Data.List(isPrefixOf)
import System.Directory (getCurrentDirectory)

import Static.DevGraph
import Static.PrintDevGraph

import Proofs.EdgeUtils
import Proofs.QualifyNames
import Proofs.DGFlattening
import Proofs.NormalForm
import Proofs.Automatic(automatic)
import Proofs.Global(globSubsume, globDecomp)
import Proofs.Local(localInference, locDecomp)
import Proofs.Composition(composition, compositionCreatingEdges)
import Proofs.HideTheoremShift(interactiveHideTheoremShift)
import Proofs.TheoremHideShift(theoremHideShift)
import Proofs.ComputeColimit(computeColimit)

import Common.DocUtils(showDoc)
import Common.Result as Res

import Driver.Options
import Driver.ReadFn(libNameToFile)

import GUI.UDGUtils
import qualified GUI.HTkUtils as HTk

import Control.Concurrent.MVar
import Common.Utils (joinWith)

import Interfaces.DataTypes

-- | Adds to the DGNodeType list style options for each type
nodeTypes :: HetcatsOpts
          -> [( DGNodeType -- Nodetype
              , Shape GA.NodeValue -- Shape
              , String -- Color
              )]
nodeTypes opts = map
  ( (\ (n, s) -> case isLocallyEmpty n of -- Add color
      True -> case nonRefType n of
        NonRefType { isProvenCons = False }
                -> (n, s, getColor opts Coral True  False)
        _       -> (n, s, getColor opts Green True  False)
      False -> case nonRefType n of
        RefType -> (n, s, getColor opts Coral False False)
        t       -> (n, s, getColor opts Coral False $ isProvenCons t)
    )
  . (\ n -> case nonRefType n of -- Add shape
      RefType                               -> (n, Box)
      NonRefType { isInternalSpec = True }  -> (n, Circle)
      NonRefType { isInternalSpec = False } -> (n, Ellipse)
    )
  ) listDGNodeTypes

-- | A Map of all nodetypes and their properties.
mapNodeTypes :: HetcatsOpts -> Map.Map DGNodeType (Shape GA.NodeValue, String)
mapNodeTypes = Map.fromList . map (\ (n, s, c) -> (n, (s, c))) . nodeTypes

-- | Adds to the DGEdgeType list style options for each type
edgeTypes :: HetcatsOpts
          -> [( DGEdgeType -- Edgetype
              , EdgePattern GA.EdgeValue -- Lineformat
              , String -- Color
              , Bool -- Is theorem
              , Bool -- Extra menu
              )]
edgeTypes opts = map
  ( (\ (e, l, c) -> case edgeTypeModInc e of -- Add menu options
      ThmType { thmEdgeType = HidingThmType } -> (e, l, c, True,  False)
      ThmType _ _                             -> (e, l, c, True,  True)
      _                                       -> (e, l, c, False, False)
    )
  . (\ (e, l) -> case edgeTypeModInc e of -- Add colors
      HidingDefType   -> (e, l, getColor opts Blue   True  $ not $ isInc e)
      FreeOrCofreeDef -> (e, l, getColor opts Blue   False $ not $ isInc e)
      ThmType { thmEdgeType = thmType
              , isProvenEdge = False } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = True, isHomThm = False }
                      -> (e, l, getColor opts Coral  True  $ not $ isInc e)
        HidingThmType -> (e, l, getColor opts Yellow False $ not $ isInc e)
        _             -> (e, l, getColor opts Coral  False $ not $ isInc e)
      ThmType { thmEdgeType = thmType
              , isProvenEdge = True } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = True, isHomThm = False }
                      -> (e, l, getColor opts Green  True  $ not $ isInc e)
        HidingThmType -> (e, l, getColor opts Green  True  $ not $ isInc e)
        _             -> (e, l, getColor opts Green  False $ not $ isInc e)
      _               -> (e, l, getColor opts Black  False $ not $ isInc e)
    )
  . (\ e -> case edgeTypeModInc e of -- Add lineformat
      ThmType { thmEdgeType = GlobalOrLocalThm { isLocalThmType = True
                                               , isHomThm = True } }
                   -> (e, Dashed)
      ThmType { thmEdgeType = GlobalOrLocalThm { isHomThm = False } }
                   -> (e, Double)
      LocalDefType -> (e, Dashed)
      HetGlobalDef -> (e, Double)
      _            -> (e, Solid)
    )
  ) listDGEdgeTypes

-- | A Map of all edgetypes and their properties.
mapEdgeTypes
  :: HetcatsOpts -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
mapEdgeTypes =
  Map.fromList . map (\ (e, l, c, _, _) -> (e, (l, c))) . edgeTypes

-- | Creates the graph. Runs makegraph
createGraph :: GInfo -> String -> ConvFunc -> LibFunc -> IO ()
createGraph gInfo@(GInfo { gi_GraphInfo = actGraphInfo
                         , gi_hetcatsOpts = opts
                         }) title convGraph showLib = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let ln = i_ln ist
       file = rmSuffix (libNameToFile opts ln) ++ prfSuffix
   deselectEdgeTypes <- newIORef []
   globMenu <- createGlobalMenu gInfo convGraph showLib deselectEdgeTypes
   GA.makegraphExt actGraphInfo
                  title
                  (createOpen gInfo file convGraph showLib)
                  (createSave gInfo file)
                  (createSaveAs gInfo file)
                  (createClose gInfo)
                  (Just (createExit gInfo))
                  globMenu
                  (createNodeTypes gInfo convGraph showLib)
                  (createEdgeTypes gInfo)

-- | Returns the open-function
createOpen :: GInfo -> FilePath -> ConvFunc -> LibFunc -> Maybe (IO ())
createOpen gInfo file convGraph showLib = Just (
  do
    maybeFilePath <- fileOpenDialog file [ ("Proof", ["*.prf"])
                                         , ("All Files", ["*"])] Nothing
    case maybeFilePath of
      Just fPath -> do
        openProofStatus gInfo fPath convGraph showLib
        return ()
      Nothing -> fail "Could not open file."
  )

-- | Returns the save-function
createSave :: GInfo -> FilePath -> Maybe (IO ())
createSave gInfo = Just . saveProofStatus gInfo

-- | Returns the saveas-function
createSaveAs :: GInfo -> FilePath -> Maybe (IO ())
createSaveAs gInfo file = Just (
  do
    maybeFilePath <- fileSaveDialog file [ ("Proof", ["*.prf"])
                                         , ("All Files", ["*"])] Nothing
    case maybeFilePath of
      Just fPath -> saveProofStatus gInfo fPath
      Nothing -> fail "Could not save file."
  )

-- | Returns the save-function
createClose :: GInfo -> IO Bool
createClose gInfo@(GInfo { windowCount = wc
                   , exitMVar = exit
                   }) = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return False
  Just ist -> do
   let le = i_libEnv ist
       ln = i_ln ist
   case Map.lookup ln le of
    Just dgraph -> case openlock dgraph of
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
createExit (GInfo {exitMVar = exit}) = putMVar exit ()

-- | Creates the global menu
createGlobalMenu :: GInfo -> ConvFunc -> LibFunc -> IORef [String]
                 -> IO [GlobalMenu]
createGlobalMenu gInfo@(GInfo { gi_hetcatsOpts = opts
                              , gi_GraphInfo = gi
                              }) convGraph showLib deselectEdgeTypes =
 do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return []
  Just ist -> do
   let ral = runAndLock gInfo
       ln = i_ln ist
   return
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
     , Button "Select Linktypes" $ showLinkTypeChoice deselectEdgeTypes
                                  (\ eList -> ral $ do
                                    GA.showAll gi
                                    GA.hideSetOfEdgeTypes gi eList
                                    GA.redisplay gi
                                  )
#endif
     , Button "Hide new proven links" $ ral $ hideNewProvedEdges gInfo
     , Menu (Just "Proofs") $ map (\ (str, cmd) ->
       -- History ? or just some partial history in ch ?
        Button str $ ral $ performProofAction gInfo
                  $ proofMenu gInfo str $ return . return . cmd ln
                  . Map.map undoRedo)
        [ ("Automatic", automatic)
        , ("Global Subsumption", globSubsume)
        , ("Global Decomposition", globDecomp)
        , ("Local Inference", localInference)
        , ("Local Decomposition (merge of rules)", locDecomp)
        , ("Composition (merge of rules)", composition)
        , ("Composition - creating new links", compositionCreatingEdges)
        ] ++
        [Button "Hide Theorem Shift"
               $ ral $ performProofAction gInfo
               $ proofMenu gInfo "Hide Theoren Shift" $
                               fmap return . interactiveHideTheoremShift ln
        ] ++
        map (\ (str, cmd) ->
               Button str
                   $ ral $ performProofAction gInfo
                   $ proofMenu gInfo str $ return . cmd ln)
        [ ("Theorem Hide Shift", theoremHideShift)
        , ("Compute Colimit", computeColimit)
        , ("Compute normal forms", const normalFormLibEnv)
        ] ++
        [ Menu (Just "Flattening") $ map ( \ (str, cmd) ->
           Button str $ ral $ performProofAction gInfo
                      $ proofMenu gInfo str $ return . cmd)
              [ ("Importings", libEnv_flattening_imports)
              , ("Disjoint unions", libEnv_flattening_dunions)
              , ("Importings and renamings", libEnv_flattening_renamings)
              , ("Hiding", libEnv_flattening_hiding)
              , ("Heterogeneity", libEnv_flattening_heterogen)
              , ("Qualify all names", qualifyLibEnv)]]
     , Button "Dump LibEnv" $ do
          ost2 <- readIORef $ intState gInfo
          case i_state ost2 of
            Nothing -> putStrLn "no lib"
            Just ist2 -> print $ prettyLibEnv $ i_libEnv ist2
     , Button "Translate Graph" $ ral $ translateGraph gInfo convGraph showLib
     , Button "Show Logic Graph" $ ral $ showLogicGraph daVinciSort
     , Button "Show Library Graph" $ ral $ showLibGraph gInfo showLib
     , Button "Save Graph for uDrawGraph" $ ral
              $ saveUDGraph gInfo (mapNodeTypes opts) $ mapEdgeTypes opts
     , Button "Save proof-script" $ ral
              $ askSaveProofScript (gi_GraphInfo gInfo) $ intState gInfo
     ])
    ]

-- | A list of all Node Types
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(DGNodeType,DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) cGraph showLib = map
  (\ (n, s, c) ->
    ( n
    , case nonRefType n of
        RefType -> createLocalMenuNodeTypeDgRef s c gInfo cGraph showLib
        NonRefType { isInternalSpec = True }
                -> createLocalMenuNodeTypeInternal s c gInfo
        NonRefType { isInternalSpec = False }
                -> createLocalMenuNodeTypeSpec s c gInfo
    )
  ) $ nodeTypes opts

-- | the edge types (share strings to avoid typos)
createEdgeTypes :: GInfo -> [(DGEdgeType,DaVinciArcTypeParms GA.EdgeValue)]
createEdgeTypes gInfo@(GInfo {gi_hetcatsOpts = opts}) =
  map (\(title, look, color, thm, extra) ->
        (title, look
            $$$ Color color
            $$$ (if thm then createLocalEdgeMenuThmEdge gInfo
                  else createLocalEdgeMenu gInfo)
            $$$ (if extra then createLocalMenuValueTitleShowConservativity
                  $$$ emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue
                  else
                    emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue))
      ) $ edgeTypes opts

-- * methods to create the local menus of the different nodetypes

createLocalMenuNode :: GInfo -> DaVinciNodeTypeParms GA.NodeValue
createLocalMenuNode gInfo = LocalMenu (Menu (Just "node menu") $ map ($ gInfo)
  [ createLocalMenuButtonShowNodeInfo
  , createLocalMenuButtonShowTheory
  , createLocalMenuButtonTranslateTheory
  , createLocalMenuTaxonomy
  , createLocalMenuButtonShowProofStatusOfNode
  , createLocalMenuButtonProveAtNode
  , createLocalMenuButtonProveStructured
#ifdef GTKGLADE
  , createLocalMenuButtonConsistencyChecker
#endif
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
createMenuButton title menuFun gInfo = Button title
  $ \ (_, descr) -> do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> return ()
      Just ist -> do
        let le = i_libEnv ist
            ln = i_ln ist
            dGraph = lookupDGraph ln le
        runAndLock gInfo $  menuFun descr dGraph
        return ()

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
createLocalMenuTaxonomy ginfo = Menu (Just "Taxonomy graphs")
  [ createMenuButton "Subsort graph" (passTh displaySubsortGraph) ginfo
  , createMenuButton "Concept graph" (passTh displayConceptGraph) ginfo ]
  where passTh displayFun descr _ =
         do
          ost <- readIORef $ intState ginfo
          case i_state ost of
           Nothing -> return ()
           Just ist -> do
             let ln = i_ln ist
                 le = i_libEnv ist
             r <- lookupTheoryOfNode le ln descr
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
    (proveAtNode (Just False) gInfo descr dgraph)) gInfo

createLocalMenuButtonProveStructured :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonProveStructured gInfo =
  createMenuButton "Prove Structured" (\descr dgraph -> performProofAction gInfo
    (proveAtNode Nothing gInfo descr dgraph)) gInfo

#ifdef GTKGLADE
createLocalMenuButtonConsistencyChecker :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonConsistencyChecker gInfo =
  createMenuButton "Consistency checker"
                   (showConsistencyChecker gInfo) gInfo
#endif

createLocalMenuButtonCCCAtNode :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (proveAtNode (Just True) gInfo) gInfo

createLocalMenuButtonShowNodeInfo :: GInfo -> ButtonMenu GA.NodeValue
createLocalMenuButtonShowNodeInfo =
  createMenuButton "Show node info" showNodeInfo

-- * methods to create the local menus for the edges

createLocalEdgeMenu :: GInfo -> LocalMenu GA.EdgeValue
createLocalEdgeMenu gInfo = LocalMenu $ Menu (Just "edge menu")
  [createLocalMenuButtonShowEdgeInfo gInfo]

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
  Button "Check conservativity"
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

-- Suggests a proof-script filename.
getProofScriptFileName :: String -> IO FilePath
getProofScriptFileName f
    | "/" `isPrefixOf` f = return $ f ++ ".hpf"
    | otherwise          = do
                           dir <- getCurrentDirectory
                           return $ dir ++ '/':f ++ ".hpf"


-- | Displays a Save-As dialog and writes the proof-script.
askSaveProofScript :: GA.GraphInfo -> IORef IntState -> IO ()
askSaveProofScript graphInfo ch =
    do
    h <- readIORef ch
    case undoList $ i_hist h of
     [] -> infoDialog "Information" "The history is empty. No file written."
     _ -> do
      ff <- getProofScriptFileName $ rmSuffix $ filename h
      maybeFilePath<- fileSaveDialog ff [("Proof Script",["*.hpf"])
                                         , ("All Files", ["*"])] Nothing
      case maybeFilePath of
        Just fPath -> do
           GA.showTemporaryMessage graphInfo "Saving proof script ..."
           saveCommandHistory ch fPath
           GA.showTemporaryMessage graphInfo $ "Proof script saved to " ++
                                            fPath ++ "!"
        Nothing -> GA.showTemporaryMessage graphInfo "Aborted!"

-- Saves the history of commands in a file.
saveCommandHistory :: IORef IntState -> String -> IO ()
saveCommandHistory c f =
    do
    h <- readIORef c
    let history = ["# automatically generated hets proof-script", "",
                   "use " ++ filename h, ""] ++ reverse (map cmdName
                                                     $ undoList $ i_hist h)
    writeFile f $ joinWith '\n' history


