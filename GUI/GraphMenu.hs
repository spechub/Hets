{-# LANGUAGE CPP #-}
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
import GUI.Utils
import GUI.UDGUtils
#ifdef GTKGLADE
import GUI.GtkLinkTypeChoice
import GUI.GtkConsistencyChecker
import GUI.GtkAutomaticProofs
#endif

import Control.Concurrent.MVar

import Data.IORef
import qualified Data.Map as Map

import System.Directory (getCurrentDirectory)
import System.FilePath

import Static.DevGraph
import Static.PrintDevGraph ()

import Static.ComputeTheory (computeTheory)
import qualified Proofs.VSE as VSE

import Common.DocUtils
import Common.Consistency

import Driver.Options (HetcatsOpts, rmSuffix, prfSuffix)
import Driver.ReadFn (libNameToFile)

import Interfaces.DataTypes
import Interfaces.Command
import Interfaces.CmdAction

import GUI.ShowRefTree

-- | Adds to the DGNodeType list style options for each type
nodeTypes :: HetcatsOpts
          -> [( DGNodeType -- Nodetype
              , Shape GA.NodeValue -- Shape
              , String -- Color
              )]
nodeTypes opts = map
  ((\ (n, s) -> if isProvenNode n then -- Add color
      if isProvenCons n
      then (n, s, getColor opts Green True False)
      else (n, s, getColor opts Yellow False True)
     else (n, s, getColor opts Coral False $ isProvenCons n))
  . \ n -> (n, if isRefType n then Box else Ellipse) -- Add shape
  ) listDGNodeTypes

-- | A Map of all nodetypes and their properties.
mapNodeTypes :: HetcatsOpts -> Map.Map DGNodeType (Shape GA.NodeValue, String)
mapNodeTypes = Map.fromList . map (\ (n, s, c) -> (n, (s, c))) . nodeTypes

-- | Adds to the DGEdgeType list style options for each type
edgeTypes :: HetcatsOpts
          -> [( DGEdgeType -- Edgetype
              , EdgePattern GA.EdgeValue -- Lineformat
              , String -- Color
              , Bool -- has conservativity
              )]
edgeTypes opts = map
  ( (\ (e, l, c) -> case edgeTypeModInc e of -- Add menu options
      ThmType { thmEdgeType = GlobalOrLocalThm _ _ } -> (e, l, c, True)
      GlobalDef -> (e, l, c, True)
      HetDef -> (e, l, c, True)
      LocalDef -> (e, l, c, True)
      _ -> (e, l, c, False)
    )
  . (\ (e, l) -> case edgeTypeModInc e of -- Add colors
      HidingDef -> (e, l, getColor opts Blue True $ not $ isInc e)
      FreeOrCofreeDef -> (e, l, getColor opts Blue False $ not $ isInc e)
      ThmType { thmEdgeType = thmType
              , isProvenEdge = False } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = Local, isHomThm = False }
                      -> (e, l, getColor opts Coral True $ not $ isInc e)
        HidingThm -> (e, l, getColor opts Yellow False $ not $ isInc e)
        _ -> (e, l, getColor opts Coral False $ not $ isInc e)
      ThmType { thmEdgeType = thmType
              , isConservativ = False } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = Local, isHomThm = False }
                      -> (e, l, getColor opts Yellow True $ not $ isInc e)
        _ -> (e, l, getColor opts Yellow False $ not $ isInc e)
      ThmType { thmEdgeType = thmType
              , isPending = True } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = Local, isHomThm = False }
                      -> (e, l, getColor opts Yellow True $ not $ isInc e)
        _ -> (e, l, getColor opts Yellow False $ not $ isInc e)
      ThmType { thmEdgeType = thmType } -> case thmType of
        GlobalOrLocalThm { isLocalThmType = Local, isHomThm = False }
                      -> (e, l, getColor opts Green True $ not $ isInc e)
        HidingThm -> (e, l, getColor opts Green True $ not $ isInc e)
        _ -> (e, l, getColor opts Green False $ not $ isInc e)
      _ -> (e, l, getColor opts Black False $ not $ isInc e)
    )
  . (\ e -> case edgeTypeModInc e of -- Add lineformat
      ThmType { thmEdgeType = GlobalOrLocalThm { isLocalThmType = Local
                                               , isHomThm = True } }
                   -> (e, Dashed)
      ThmType { thmEdgeType = GlobalOrLocalThm { isHomThm = False } }
                   -> (e, Double)
      LocalDef -> (e, Dashed)
      HetDef -> (e, Double)
      _ -> (e, Solid)
    )
  ) listDGEdgeTypes

-- | A Map of all edgetypes and their properties.
mapEdgeTypes
  :: HetcatsOpts -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
mapEdgeTypes =
  Map.fromList . map (\ (e, l, c, _) -> (e, (l, c))) . edgeTypes

-- | Creates the graph. Runs makegraph
createGraph :: GInfo -> String -> ConvFunc -> LibFunc -> IO ()
createGraph gInfo@(GInfo { graphInfo = gi
                         , hetcatsOpts = hetOpts
                         , options = opts
                         , libName = ln }) title convGraph showLib = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
    Nothing -> return ()
    Just _ -> do
      let file = rmSuffix (libNameToFile ln) ++ prfSuffix
      deselectEdgeTypes <- newIORef []
      globMenu <- createGlobalMenu gInfo showLib deselectEdgeTypes
      GA.makeGraph gi
                   title
                   (createOpen gInfo file convGraph showLib)
                   (createSave gInfo file)
                   (createSaveAs gInfo file)
                   (createClose gInfo)
                   (Just (createExit gInfo))
                   globMenu
                   (createNodeTypes gInfo convGraph showLib)
                   (createEdgeTypes gInfo)
                   (getColor hetOpts Purple False False)
                   $ runAndLock gInfo $ do
                       flags <- readIORef opts
                       writeIORef opts $ flags { flagHideNodes = False}
                       updateGraph gInfo []

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

-- | Returns the close-function
createClose :: GInfo -> IO Bool
createClose gInfo@(GInfo { windowCount = wc
                         , openGraphs = oGrRef
                         , exitMVar = exit
                         , libName = ln }) = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return False
  Just ist -> do
   let le = i_libEnv ist
   case Map.lookup ln le of
    Just dgraph -> case openlock dgraph of
        Just lock -> do
          notopen <- isEmptyMVar lock
          if notopen then
            error "development graph seems to be closed already"
            else takeMVar lock
        Nothing -> error $ "MVar of " ++ show ln ++ " not initialized"
    Nothing -> error $ "development graph with libname " ++ show ln
                       ++ " does not exist"
   count <- takeMVar wc
   if count <= 1
     then putMVar exit ()
     else do
       putMVar wc $ count - 1
       oGraphs <- readIORef oGrRef
       writeIORef oGrRef $ Map.delete ln oGraphs
   return True

-- | Returns the exit-function
createExit :: GInfo -> IO ()
createExit (GInfo {exitMVar = exit}) = putMVar exit ()

-- | Creates the global menu
createGlobalMenu :: GInfo -> LibFunc -> IORef [String]
                 -> IO [GlobalMenu]
createGlobalMenu gInfo@
  (GInfo { hetcatsOpts = opts
         , libName = ln
#ifdef GTKGLADE
         , graphInfo = gi
#endif
         }) showLib
#ifdef GTKGLADE
  deselectEdgeTypes
#else
  _
#endif
 = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return []
  Just _ -> do
   let ral = runAndLock gInfo
       performProofMenuAction cmd =
           ral . proofMenu gInfo cmd
       mkGlobProofButton cmd =
         Button (menuTextGlobCmd cmd) . performProofMenuAction (GlobCmd cmd)
   return
    [GlobalMenu (Menu Nothing
     [ Button "Undo" $ ral $ undo gInfo True
     , Button "Redo" $ ral $ undo gInfo False
     , Menu (Just "Hide/Show names/nodes/edges")
        [ Button "Hide/Show internal node names"
                 $ ral $ toggleHideNames gInfo
        , Button "Hide/Show unnamed nodes without open proofs"
                 $ ral $ toggleHideNodes gInfo
        , Button "Hide/Show newly added proven edges"
                 $ ral $ toggleHideEdges gInfo
      ]
     , Button "Focus node" $ ral $ focusNode gInfo
#ifdef GTKGLADE
     , Button "Select Linktypes" $ showLinkTypeChoice deselectEdgeTypes
                                   (\ eTypes -> ral $ do
                                     GA.hideSetOfEdgeTypes gi eTypes
                                     updateGraph gInfo []
                                   )
     , Button "Consistency checker"
         (performProofMenuAction (GlobCmd CheckConsistencyCurrent)
           $ showConsistencyChecker Nothing gInfo)
     , Button "Automatic proofs"
         (performProofMenuAction (GlobCmd ProveCurrent)
           $ showAutomaticProofs gInfo)
#endif
     , Menu (Just "Proofs") $ map (\ (cmd, act) ->
       -- History ? or just some partial history in ch ?
        mkGlobProofButton cmd $ return . return . act ln) globLibAct
        ++ map (\ (cmd, act) -> mkGlobProofButton cmd $ return . act ln)
           globLibResultAct
        ++ [ Menu (Just "Flattening") $ map ( \ (cmd, act) ->
           mkGlobProofButton cmd $ return . act) globResultAct ]
     , Button "Dump Development Graph" $ do
          ost2 <- readIORef $ intState gInfo
          case i_state ost2 of
            Nothing -> putStrLn "no lib"
            Just ist2 -> print . pretty . lookupDGraph (i_ln ist2)
              $ i_libEnv ist2
     , Button "Show Library Graph" $ ral $ showLibGraph gInfo showLib
     , Button "Show RefinementTree" $ ral $ showLibGraph gInfo showRefTree
     , Button "Save Graph for uDrawGraph" $ ral
              $ saveUDGraph gInfo (mapNodeTypes opts) $ mapEdgeTypes opts
     , Button "Save proof-script" $ ral
              $ askSaveProofScript (graphInfo gInfo) $ intState gInfo
     ])
    ]

-- | A list of all Node Types
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(DGNodeType, DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gInfo@(GInfo {hetcatsOpts = opts}) cGraph showLib = map
  (\ (n, s, c) -> (n, if isRefType n
    then createMenuNodeRef s c gInfo cGraph showLib $ isInternalSpec n
    else createMenuNode s c gInfo $ isInternalSpec n)) $ nodeTypes opts

-- | the edge types (share strings to avoid typos)
createEdgeTypes :: GInfo -> [(DGEdgeType, DaVinciArcTypeParms GA.EdgeValue)]
createEdgeTypes gInfo@(GInfo {hetcatsOpts = opts}) =
  map (\ (title, look, color, hasCons) ->
        (title, look
          $$$ Color color
          $$$ (if hasCons then createEdgeMenuConsEdge gInfo
                else createEdgeMenu gInfo)
          $$$ (if hasCons then createMenuValueTitleShowConservativity
                $$$ emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue
                else emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue))
      ) $ edgeTypes opts

-- * methods to create the local menus of the different nodetypes

titleNormal :: ValueTitle (String, t)
titleNormal = ValueTitle (\ (s, _) -> return s)

titleInternal :: GInfo -> ValueTitleSource (String, t)
titleInternal (GInfo { internalNames = updaterIORef }) =
  ValueTitleSource (\ (s, _) -> do
                     b <- newSimpleBroadcaster ""
                     updater <- readIORef updaterIORef
                     let upd = (s, applySimpleUpdate b)
                     writeIORef updaterIORef $ upd : updater
                     return $ toSimpleSource b)

-- | local menu for the nodetypes spec and locallyEmpty_spec
createMenuNode :: Shape GA.NodeValue -> String -> GInfo -> Bool
               -> DaVinciNodeTypeParms GA.NodeValue
createMenuNode shape color gInfo internal = shape
  $$$ Color color
  $$$ (if internal then Just $ titleInternal gInfo else Nothing)
  $$$? (if internal then Nothing else Just titleNormal)
  $$$? LocalMenu (Menu Nothing (map ($ gInfo)
        [ createMenuButtonShowNodeInfo
        , createMenuButtonShowTheory
        , createMenuButtonTranslateTheory
        , createMenuTaxonomy
        , createMenuButtonShowProofStatusOfNode
        , createMenuButtonProveAtNode
        , createMenuButtonProveStructured
#ifdef GTKGLADE
        , createMenuButtonCCCAtNode
#endif
        , createMenuButtonCheckCons
        ]))
  $$$ emptyNodeTypeParms


-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createMenuNodeRef :: Shape GA.NodeValue -> String -> GInfo -> ConvFunc
                  -> LibFunc -> Bool -> DaVinciNodeTypeParms GA.NodeValue
createMenuNodeRef shape color gInfo convGraph showLib internal = shape
  $$$ Color color
  $$$ (if internal then Just $ titleInternal gInfo else Nothing)
  $$$? (if internal then Nothing else Just titleNormal)
  $$$? LocalMenu (Menu Nothing
        [ createMenuButtonShowNodeInfo gInfo
        , createMenuButtonShowTheory gInfo
        , createMenuButtonShowProofStatusOfNode gInfo
        , createMenuButtonProveAtNode gInfo
        , Button "Show referenced library"
            (\ (_, n) -> showReferencedLibrary n gInfo convGraph showLib)
        ])
  $$$ emptyNodeTypeParms

type ButtonMenu a = MenuPrim (Maybe String) (a -> IO ())

-- | menu button for local menus
createMenuButton :: String -> (Int -> DGraph -> IO ())
                 -> GInfo -> ButtonMenu GA.NodeValue
createMenuButton title menuFun gInfo@(GInfo { libName = ln }) = Button title
  $ \ (_, descr) -> do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> return ()
      Just ist -> do
        let le = i_libEnv ist
            dGraph = lookupDGraph ln le
        menuFun descr dGraph
        return ()

createMenuButtonShowTheory :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowTheory gInfo =
  createMenuButton "Show theory" (getTheoryOfNode gInfo) gInfo

createMenuButtonTranslateTheory :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonTranslateTheory gInfo =
  createMenuButton "Translate theory" (translateTheoryOfNode gInfo) gInfo

-- | create a sub menu for taxonomy visualisation
createMenuTaxonomy :: GInfo -> ButtonMenu GA.NodeValue
createMenuTaxonomy gInfo = let
  passTh displayFun descr _ = do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> return ()
      Just ist -> case computeTheory (i_libEnv ist) (libName gInfo) descr of
        Just th -> displayFun (show descr) th
        Nothing -> errorDialog "Error"
          $ "no global theory for node " ++ show descr
  in Menu (Just "Taxonomy graphs")
    [ createMenuButton "Subsort graph" (passTh displaySubsortGraph) gInfo
    , createMenuButton "Concept graph" (passTh displayConceptGraph) gInfo ]

createMenuButtonShowProofStatusOfNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowProofStatusOfNode gInfo =
  createMenuButton "Show proof status" (showProofStatusOfNode gInfo) gInfo

createMenuButtonProveAtNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonProveAtNode gInfo =
  createMenuButton "Prove" (proveAtNode gInfo) gInfo

createMenuButtonProveStructured :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonProveStructured gInfo =
  createMenuButton "Prove VSE Structured" (\ descr _ ->
    proofMenu gInfo (SelectCmd Prover $ "VSE structured: " ++ show descr)
              $ VSE.prove (libName gInfo, descr)) gInfo

#ifdef GTKGLADE
createMenuButtonCCCAtNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonCCCAtNode gInfo =
  createMenuButton "Check consistency" (consCheckNode gInfo) gInfo

consCheckNode :: GInfo -> Int -> DGraph -> IO ()
consCheckNode gInfo descr _ = proofMenu gInfo (GlobCmd CheckConsistencyCurrent)
  $ showConsistencyChecker (Just descr) gInfo
#endif

createMenuButtonCheckCons :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonCheckCons gInfo =
  createMenuButton "Check conservativity"
    (checkconservativityOfNode gInfo) gInfo

createMenuButtonShowNodeInfo :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowNodeInfo =
  createMenuButton "Show node info" showNodeInfo

-- * methods to create the local menus for the edges

createEdgeMenu :: GInfo -> LocalMenu GA.EdgeValue
createEdgeMenu = LocalMenu . createMenuButtonShowEdgeInfo

createEdgeMenuConsEdge :: GInfo -> LocalMenu GA.EdgeValue
createEdgeMenuConsEdge gInfo = LocalMenu $ Menu Nothing
  [ createMenuButtonShowEdgeInfo gInfo
  , createMenuButtonCheckconservativityOfEdge gInfo]

createMenuButtonShowEdgeInfo :: GInfo -> ButtonMenu GA.EdgeValue
createMenuButtonShowEdgeInfo _ = Button "Show info"
  (\ (_, EdgeId descr, maybeLEdge) -> showEdgeInfo descr maybeLEdge)

createMenuButtonCheckconservativityOfEdge :: GInfo
                                               -> ButtonMenu GA.EdgeValue
createMenuButtonCheckconservativityOfEdge gInfo =
  Button "Check conservativity"
    (\ (_, EdgeId descr, maybeLEdge) ->
      checkconservativityOfEdge descr gInfo maybeLEdge)

createMenuValueTitleShowConservativity :: ValueTitle GA.EdgeValue
createMenuValueTitleShowConservativity = ValueTitle
  (\ (_, _, maybeLEdge) -> case maybeLEdge of
    Just (_, _, edgelab) -> case dgl_type edgelab of
      ScopedLink _ _ (ConsStatus c cp status) -> return (showCons c cp status)
      _ -> return ""
    Nothing -> return "")
  where
    showCons :: Conservativity -> Conservativity -> ThmLinkStatus -> String
    showCons c cp status = case (c, cp, status) of
      (None, None, _) -> ""
      (None, _, LeftOpen) -> ""
      (_, _, LeftOpen) -> show c ++ "?"
      _ -> show cp

-- Suggests a proof-script filename.
getProofScriptFileName :: String -> IO FilePath
getProofScriptFileName f = let fn = f <.> "hpf" in
  if isAbsolute fn then return fn else
     fmap (</> fn) getCurrentDirectory

-- | Displays a Save-As dialog and writes the proof-script.
askSaveProofScript :: GA.GraphInfo -> IORef IntState -> IO ()
askSaveProofScript gi ch = do
  h <- readIORef ch
  case undoList $ i_hist h of
   [] -> infoDialog "Information" "The history is empty. No file written."
   _ -> do
     ff <- getProofScriptFileName $ rmSuffix $ filename h
     maybeFilePath <- fileSaveDialog ff [ ("Proof Script", ["*.hpf"])
                                        , ("All Files", ["*"])] Nothing
     case maybeFilePath of
       Just fPath -> do
         GA.showTemporaryMessage gi "Saving proof script ..."
         saveCommandHistory ch fPath
         GA.showTemporaryMessage gi $ "Proof script saved to " ++ fPath ++ "!"
       Nothing -> GA.showTemporaryMessage gi "Aborted!"

-- Saves the history of commands in a file.
saveCommandHistory :: IORef IntState -> String -> IO ()
saveCommandHistory c f = do
  h <- readIORef c
  let history = [ "# automatically generated hets proof-script", ""
                , "use " ++ filename h, ""]
                ++ reverse (map (showCmd . command) $ undoList $ i_hist h)
  writeFile f $ unlines history
