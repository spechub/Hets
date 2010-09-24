{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  Menu creation functions for the Graphdisplay
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2002-2008
License     :  GPLv2 or higher, see LICENSE.txt

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
import GUI.GtkAddSentence
#endif

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
createGraph gi title convGraph showLib = do
  ost <- readIORef $ intState gi
  case i_state ost of
    Nothing -> return ()
    Just _ -> do
      let ln = libName gi
          opts = options gi
          file = rmSuffix (libNameToFile ln) ++ prfSuffix
      deselectEdgeTypes <- newIORef []
      globMenu <- createGlobalMenu gi showLib deselectEdgeTypes
      GA.makeGraph (graphInfo gi)
                   title
                   (createOpen gi file convGraph showLib)
                   (createSave gi file)
                   (createSaveAs gi file)
                   (createClose gi)
                   (Just (exitGInfo gi))
                   globMenu
                   (createNodeTypes gi convGraph showLib)
                   (createEdgeTypes gi)
                   (getColor (hetcatsOpts gi) Purple False False)
                   $ runAndLock gi $ do
                       flags <- readIORef opts
                       writeIORef opts $ flags { flagHideNodes = False}
                       updateGraph gi []

-- | Returns the open-function
createOpen :: GInfo -> FilePath -> ConvFunc -> LibFunc -> Maybe (IO ())
createOpen gi file convGraph showLib = Just (
  do
    maybeFilePath <- fileOpenDialog file [ ("Proof", ["*.prf"])
                                         , ("All Files", ["*"])] Nothing
    case maybeFilePath of
      Just fPath -> do
        openProofStatus gi fPath convGraph showLib
        return ()
      Nothing -> fail "Could not open file."
  )

-- | Returns the save-function
createSave :: GInfo -> FilePath -> Maybe (IO ())
createSave gi = Just . saveProofStatus gi

-- | Returns the saveas-function
createSaveAs :: GInfo -> FilePath -> Maybe (IO ())
createSaveAs gi file = Just (
  do
    maybeFilePath <- fileSaveDialog file [ ("Proof", ["*.prf"])
                                         , ("All Files", ["*"])] Nothing
    case maybeFilePath of
      Just fPath -> saveProofStatus gi fPath
      Nothing -> fail "Could not save file."
  )

-- | Returns the close-function
createClose :: GInfo -> IO Bool
createClose gi = do
   let oGrRef = openGraphs gi
   updateWindowCount gi pred
   oGraphs <- readIORef oGrRef
   writeIORef oGrRef $ Map.delete (libName gi) oGraphs
   return True

-- | Creates the global menu
createGlobalMenu :: GInfo -> LibFunc -> IORef [String]
                 -> IO [GlobalMenu]
createGlobalMenu gi showLib
#ifdef GTKGLADE
  deselectEdgeTypes
#else
  _
#endif
 = do
 ost <- readIORef $ intState gi
 case i_state ost of
  Nothing -> return []
  Just _ -> do
   let ln = libName gi
       opts = hetcatsOpts gi
       ral = runAndLock gi
       performProofMenuAction cmd =
           ral . proofMenu gi cmd
       mkGlobProofButton cmd =
         Button (menuTextGlobCmd cmd) . performProofMenuAction (GlobCmd cmd)
   return
    [GlobalMenu (Menu Nothing
     [ Button "Undo" $ ral $ undo gi True
     , Button "Redo" $ ral $ undo gi False
     , Menu (Just "Hide/Show names/nodes/edges")
        [ Button "Hide/Show internal node names"
                 $ ral $ toggleHideNames gi
        , Button "Hide/Show unnamed nodes without open proofs"
                 $ ral $ toggleHideNodes gi
        , Button "Hide/Show newly added proven edges"
                 $ ral $ toggleHideEdges gi
      ]
     , Button "Focus node" $ ral $ focusNode gi
#ifdef GTKGLADE
     , Button "Select Linktypes" $ showLinkTypeChoice deselectEdgeTypes
       $ \ eTypes -> ral $ do
             GA.hideSetOfEdgeTypes (graphInfo gi) eTypes
             updateGraph gi []
     , Button "Consistency checker"
         (performProofMenuAction (GlobCmd CheckConsistencyCurrent)
           $ showConsistencyChecker Nothing gi)
     , Button "Automatic proofs"
         (performProofMenuAction (GlobCmd ProveCurrent)
           $ showAutomaticProofs gi)
#endif
     , Menu (Just "Proofs") $ map (\ (cmd, act) ->
        mkGlobProofButton cmd $ return . return . act ln) globLibAct
        ++ map (\ (cmd, act) -> mkGlobProofButton cmd $ return . act ln)
           globLibResultAct
        ++ [ Menu (Just "Flattening") $ map ( \ (cmd, act) ->
           mkGlobProofButton cmd $ return . act) globResultAct ]
     , Button "Dump Development Graph" $ do
          ost2 <- readIORef $ intState gi
          case i_state ost2 of
            Nothing -> putStrLn "no lib"
            Just ist2 -> print . pretty . lookupDGraph (i_ln ist2)
              $ i_libEnv ist2
     , Button "Show Library Graph" $ ral $ showLibGraph gi showLib
     , Button "Show RefinementTree" $ ral $ showLibGraph gi showRefTree
     , Button "Save Graph for uDrawGraph" $ ral
              $ saveUDGraph gi (mapNodeTypes opts) $ mapEdgeTypes opts
     , Button "Save proof-script" $ ral
              $ askSaveProofScript (graphInfo gi) $ intState gi
     ])
    ]

-- | A list of all Node Types
createNodeTypes :: GInfo -> ConvFunc -> LibFunc
                -> [(DGNodeType, DaVinciNodeTypeParms GA.NodeValue)]
createNodeTypes gi cGraph showLib = map
  (\ (n, s, c) -> (n, if isRefType n
    then createMenuNodeRef s c gi cGraph showLib $ isInternalSpec n
    else createMenuNode s c gi $ isInternalSpec n)) $ nodeTypes $ hetcatsOpts gi

-- | the edge types (share strings to avoid typos)
createEdgeTypes :: GInfo -> [(DGEdgeType, DaVinciArcTypeParms GA.EdgeValue)]
createEdgeTypes gi =
  map (\ (title, look, color, hasCons) ->
        (title, look
          $$$ Color color
          $$$ (if hasCons then createEdgeMenuConsEdge gi
                else createEdgeMenu gi)
          $$$ (if hasCons then createMenuValueTitleShowConservativity
                $$$ emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue
                else emptyArcTypeParms :: DaVinciArcTypeParms GA.EdgeValue))
      ) $ edgeTypes $ hetcatsOpts gi

-- * methods to create the local menus of the different nodetypes

titleNormal :: ValueTitle (String, t)
titleNormal = ValueTitle $ return . fst

titleInternal :: GInfo -> ValueTitleSource (String, t)
titleInternal gi =
  ValueTitleSource (\ (s, _) -> do
                     b <- newSimpleBroadcaster ""
                     let updaterIORef = internalNames gi
                     updater <- readIORef updaterIORef
                     let upd = (s, applySimpleUpdate b)
                     writeIORef updaterIORef $ upd : updater
                     return $ toSimpleSource b)

-- | local menu for the nodetypes spec and locallyEmpty_spec
createMenuNode :: Shape GA.NodeValue -> String -> GInfo -> Bool
               -> DaVinciNodeTypeParms GA.NodeValue
createMenuNode shape color gi internal = shape
  $$$ Color color
  $$$ (if internal then Just $ titleInternal gi else Nothing)
  $$$? (if internal then Nothing else Just titleNormal)
  $$$? LocalMenu (Menu Nothing (map ($ gi)
        [ createMenuButtonShowNodeInfo
        , createMenuButtonShowTheory
        , createMenuButtonTranslateTheory
        , createMenuTaxonomy
        , createMenuButtonShowProofStatusOfNode
        , createMenuButtonProveAtNode
        , createMenuButtonProveStructured
#ifdef GTKGLADE
        , createMenuButtonDisproveAtNode
        , createMenuButtonAddSentence
        , createMenuButtonCCCAtNode
#endif
        , createMenuButtonCheckCons
        ]))
  $$$ emptyNodeTypeParms


-- | local menu for the nodetypes dg_ref and locallyEmpty_dg_ref
createMenuNodeRef :: Shape GA.NodeValue -> String -> GInfo -> ConvFunc
                  -> LibFunc -> Bool -> DaVinciNodeTypeParms GA.NodeValue
createMenuNodeRef shape color gi convGraph showLib internal = shape
  $$$ Color color
  $$$ (if internal then Just $ titleInternal gi else Nothing)
  $$$? (if internal then Nothing else Just titleNormal)
  $$$? LocalMenu (Menu Nothing
        [ createMenuButtonShowNodeInfo gi
        , createMenuButtonShowTheory gi
        , createMenuButtonShowProofStatusOfNode gi
        , createMenuButtonProveAtNode gi
        , Button "Show referenced library"
            (\ (_, n) -> showReferencedLibrary n gi convGraph showLib)
        ])
  $$$ emptyNodeTypeParms

type ButtonMenu a = MenuPrim (Maybe String) (a -> IO ())

-- | menu button for local menus
createMenuButton :: String -> (Int -> DGraph -> IO ())
                 -> GInfo -> ButtonMenu GA.NodeValue
createMenuButton title menuFun gi = Button title
  $ \ (_, descr) -> do
    ost <- readIORef $ intState gi
    case i_state ost of
      Nothing -> return ()
      Just ist -> do
        let le = i_libEnv ist
            dGraph = lookupDGraph (libName gi) le
        menuFun descr dGraph
        return ()

createMenuButtonShowTheory :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowTheory gi =
  createMenuButton "Show theory" (getTheoryOfNode gi) gi

createMenuButtonTranslateTheory :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonTranslateTheory gi =
  createMenuButton "Translate theory" (translateTheoryOfNode gi) gi

-- | create a sub menu for taxonomy visualisation
createMenuTaxonomy :: GInfo -> ButtonMenu GA.NodeValue
createMenuTaxonomy gi = let
  passTh displayFun descr _ = do
    ost <- readIORef $ intState gi
    case i_state ost of
      Nothing -> return ()
      Just ist -> case computeTheory (i_libEnv ist) (libName gi) descr of
        Just th -> displayFun (show descr) th
        Nothing -> errorDialog "Error"
          $ "no global theory for node " ++ show descr
  in Menu (Just "Taxonomy graphs")
    [ createMenuButton "Subsort graph" (passTh displaySubsortGraph) gi
    , createMenuButton "Concept graph" (passTh displayConceptGraph) gi ]

createMenuButtonShowProofStatusOfNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowProofStatusOfNode gi =
  createMenuButton "Show proof status" (showProofStatusOfNode gi) gi

createMenuButtonProveAtNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonProveAtNode gi =
  createMenuButton "Prove" (proveAtNode gi) gi

createMenuButtonDisproveAtNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonDisproveAtNode gi =
  createMenuButton "Disprove" (disproveAtNode gi) gi

createMenuButtonProveStructured :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonProveStructured gi =
  createMenuButton "Prove VSE Structured" (\ descr _ ->
    proofMenu gi (SelectCmd Prover $ "VSE structured: " ++ show descr)
              $ VSE.prove (libName gi, descr)) gi

#ifdef GTKGLADE
createMenuButtonCCCAtNode :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonCCCAtNode gi =
  createMenuButton "Check consistency" (consCheckNode gi) gi

consCheckNode :: GInfo -> Int -> DGraph -> IO ()
consCheckNode gi descr _ = proofMenu gi (GlobCmd CheckConsistencyCurrent)
  $ showConsistencyChecker (Just descr) gi

createMenuButtonAddSentence :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonAddSentence gi =
  createMenuButton "Add sentence" (gtkAddSentence gi) gi
#endif

createMenuButtonCheckCons :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonCheckCons gi =
  createMenuButton "Check conservativity"
    (checkconservativityOfNode gi) gi

createMenuButtonShowNodeInfo :: GInfo -> ButtonMenu GA.NodeValue
createMenuButtonShowNodeInfo =
  createMenuButton "Show node info" showNodeInfo

-- * methods to create the local menus for the edges

createEdgeMenu :: GInfo -> LocalMenu GA.EdgeValue
createEdgeMenu = LocalMenu . createMenuButtonShowEdgeInfo

createEdgeMenuConsEdge :: GInfo -> LocalMenu GA.EdgeValue
createEdgeMenuConsEdge gi = LocalMenu $ Menu Nothing
  [ createMenuButtonShowEdgeInfo gi
  , createMenuButtonCheckconservativityOfEdge gi]

createMenuButtonShowEdgeInfo :: GInfo -> ButtonMenu GA.EdgeValue
createMenuButtonShowEdgeInfo _ = Button "Show info"
  (\ (_, EdgeId descr, maybeLEdge) -> showEdgeInfo descr maybeLEdge)

createMenuButtonCheckconservativityOfEdge :: GInfo
                                               -> ButtonMenu GA.EdgeValue
createMenuButtonCheckconservativityOfEdge gi =
  Button "Check conservativity"
    (\ (_, EdgeId descr, maybeLEdge) ->
      checkconservativityOfEdge descr gi maybeLEdge)

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
