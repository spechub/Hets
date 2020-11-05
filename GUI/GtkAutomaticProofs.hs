{- |
Module      :  ./GUI/GtkAutomaticProofs.hs
Description :  Gtk GUI for automatic proving procedure of multiple nodes
Copyright   :  (c) Simon Ulbricht, Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the automatic proofs module.
-}

module GUI.GtkAutomaticProofs
  (showAutomaticProofs, Finder (..))
  where

import Graphics.UI.Gtk

import qualified GUI.Glade.NodeChecker as ConsistencyChecker
import GUI.GraphTypes
import GUI.GtkUtils

import Static.DevGraph
import Static.DgUtils
import Static.PrintDevGraph ()
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Interfaces.GenericATPState (guiDefaultTimeLimit)

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism (..))
import Logic.Prover

import Comorphisms.LogicGraph (logicGraph)

import Common.LibName (LibName)
import Common.AutoProofUtils
import Common.Result
import Common.ResultT

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Monad (foldM_, join, when)
import Control.Monad.Trans

import Proofs.AbstractState

import qualified Data.HashMap.Lazy as Map
import Data.List
import Data.Maybe

import Interfaces.Utils

-- | Data structure for saving the user-selected prover and comorphism
data Finder = Finder { fName :: String
                     , finder :: G_prover
                     , comorphism :: [AnyComorphism]
                     , selected :: Int }

instance Eq Finder where
  f1 == f2 = fName f1 == fName f2 && comorphism f1 == comorphism f2

-- | Displays the consistency checker window
showAutomaticProofs :: GInfo -> LibEnv -> IO (Result LibEnv)
showAutomaticProofs ginf@(GInfo { libName = ln }) le = do
  wait <- newEmptyMVar
  showProverWindow ginf wait ln le
  le' <- takeMVar wait
  return $ Result [] $ Just le'

-- | Displays the consistency checker window
showProverWindow :: GInfo -> MVar LibEnv -> LibName -> LibEnv -> IO ()
showProverWindow ginf res ln le = postGUIAsync $ do
  builder <- getGTKBuilder ConsistencyChecker.get
  -- get objects
  window <- builderGetObject builder castToWindow "NodeChecker"
  btnClose <- builderGetObject builder castToButton "btnClose"
  btnResults <- builderGetObject builder castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes <- builderGetObject builder castToTreeView "trvNodes"
  btnNodesAll <- builderGetObject builder castToButton "btnNodesAll"
  btnNodesNone <- builderGetObject builder castToButton "btnNodesNone"
  btnNodesInvert <- builderGetObject builder castToButton "btnNodesInvert"
  btnNodesUnchecked <- builderGetObject builder castToButton "btnNodesUnchecked"
  btnNodesTimeout <- builderGetObject builder castToButton "btnNodesTimeout"
  cbInclThms <- builderGetObject builder castToCheckButton "cbInclThms"
  -- get checker view and buttons
  cbComorphism <- builderGetObject builder castToComboBox "cbComorphism"
  lblSublogic <- builderGetObject builder castToLabel "lblSublogic"
  sbTimeout <- builderGetObject builder castToSpinButton "sbTimeout"
  btnCheck <- builderGetObject builder castToButton "btnCheck"
  btnStop <- builderGetObject builder castToButton "btnStop"
  -- btnFineGrained    <- builderGetObject builder castToButton "btnFineGrained"
  trvFinder <- builderGetObject builder castToTreeView "trvFinder"
  toolLabel <- builderGetObject builder castToLabel "label1"
  labelSetLabel toolLabel "Pick prover"
  windowSetTitle window "AutomaticProofs"
  spinButtonSetValue sbTimeout $ fromIntegral guiDefaultTimeLimit

  let widgets = [ toWidget sbTimeout
                , toWidget cbComorphism
                , toWidget lblSublogic ]
      checkWidgets = widgets ++ [ toWidget btnClose
                                , toWidget btnNodesAll
                                , toWidget btnNodesNone
                                , toWidget btnNodesInvert
                                , toWidget btnNodesUnchecked
                                , toWidget btnNodesTimeout
                                , toWidget btnResults ]
      switch b = do
        widgetSetSensitive btnStop $ not b
        widgetSetSensitive btnCheck b

  toggleButtonSetActive cbInclThms False

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait <- newEmptyMVar
  mView <- newEmptyMVar

  let dg = lookupDGraph ln le
      nodes = initFNodes $ labNodesDG dg

  -- setup data
  listNodes <- setListData trvNodes show $ sort nodes
  listFinder <- setListData trvFinder fName []

  -- setup comorphism combobox
  comboBoxSetModelText cbComorphism
  shC <- after cbComorphism changed
    $ setSelectedComorphism trvFinder listFinder cbComorphism

  -- setup view selection actions
  let update = do
        mf <- getSelectedSingle trvFinder listFinder
        updateComorphism trvFinder listFinder cbComorphism shC
        widgetSetSensitive btnCheck $ isJust mf
  setListSelectorSingle trvFinder update

  let upd = updateNodes trvNodes listNodes
              (\ s -> do
                labelSetLabel lblSublogic $ show s
                updateFinder trvFinder listFinder s )
              (do
                labelSetLabel lblSublogic "No sublogic"
                listStoreClear listFinder
                activate widgets False
                widgetSetSensitive btnCheck False)
              (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings

  {- this function handles the selction of nodes, getting as input parameter
  a function f (FNode -> Bool). -}
  let selectWith f u = do
        signalBlock shN
        sel <- treeViewGetSelection trvNodes
        treeSelectionSelectAll sel
        rs <- treeSelectionGetSelectedRows sel
        mapM_ ( \ ~p@(row : []) -> do
          fn <- listStoreGetValue listNodes row
          (if f fn then treeSelectionSelectPath else treeSelectionUnselectPath)
            sel p) rs
        signalUnblock shN
        u

  onClicked btnNodesUnchecked
    $ selectWith unchecked upd
  onClicked btnNodesTimeout $ selectWith timedout upd

  onClicked btnResults $ showModelView mView "Models" listNodes []
  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    inclThms <- toggleButtonGetActive cbInclThms
    (prgBar, exit) <- progressBar "Proving" "please wait..."
    nodes' <- getSelectedMultiple trvNodes listNodes
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Automatic Proofs: internal error"
      Just (_, f) -> return f
    switch False
    tid <- forkIO $ do
      performAutoProof ginf inclThms timeout prgBar f listNodes nodes'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of automatic proofs" listNodes []
        signalBlock shN
        sortNodes trvNodes listNodes
        signalUnblock shN
        upd
        activate checkWidgets True
        exit

  {- after window is closed, the results are written back into the DGraph.
  for each node a DGChange object is created and applied to the DGraph. -}
  onDestroy window $ do
    nodes' <- listStoreToList listNodes
    let dg' = foldl (\ cs fn ->
                      {- where the proving did not return anything, the node is
                      not updated -}
                      if unchecked fn then cs
                          else updateLabelTheory le ln cs (node fn) (results fn)
                    ) dg nodes'

    putMVar res $ Map.insert ln (groupHistory dg (DGRule "autoproof") dg') le

  -- setting up the selected items at startup
  selectWith (not . allProved) upd

  -- TODO select SPASS Prover if possible
  widgetShow window


performAutoProof :: GInfo
                    -- include proven Theorems in subsequent proofs
                  -> Bool
                    -- Timeout (sec)
                  -> Int
                    -- Progress bar
                  -> (Double -> String -> IO ())
                    -- selcted Prover and Comorphism
                  -> Finder
                    -- Display function for node selection box
                  -> ListStore FNode
                    -- selected nodes
                  -> [(Int, FNode)]
                    {- no return value, since results are stored by changing
                    FNode data -}
                  -> IO ()
performAutoProof gi inclThms timeout update (Finder _ pr cs i) listNodes nodes =
  let count' = fromIntegral $ length nodes
      c = cs !! i
  in foldM_ (\ count (row, fn) -> do
           postGUISync $ update (count / count') $ name fn
           res <- maybe (return Nothing) (\ g_th -> do
                    Result ds ms <- runResultT
                        (do
                          (a, b) <- autoProofAtNode inclThms timeout [] [] g_th
                            (pr, c)
                          liftIO $ addCommandHistoryToState (intState gi)
                            (fst b) (Just (pr, c)) (snd b) (name fn)
                            (True, timeout)
                          return a)
                    maybe (fail $ showRelDiags 1 ds) (return . Just . fst) ms)
                  $ globalTheory $ snd $ node fn
           case res of
             Just gt -> postGUISync $ listStoreSetValue listNodes row
               fn { results = propagateProofs (results fn) gt }
             Nothing -> return ()
           return $ count + 1) 0 nodes

sortNodes :: TreeView -> ListStore FNode -> IO ()
sortNodes trvNodes listNodes = do
  sel <- getSelectedMultiple trvNodes listNodes
  nodes <- listStoreToList listNodes
  let sn = sort nodes
  updateListData listNodes sn
  selector <- treeViewGetSelection trvNodes
  mapM_ (\ (_, FNode { name = n }) -> treeSelectionSelectPath selector
      [fromMaybe (error "Node not found!") $ findIndex ((n ==) . name) sn]
    ) sel

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore FNode -> (G_sublogics -> IO ())
            -> IO () -> IO () -> IO ()
updateNodes view listNodes update lock unlock = do
  nodes <- getSelectedMultiple view listNodes
  if null nodes then lock
    else let sls = map (sublogic . snd) nodes in
      maybe lock (\ sl -> unlock >> update sl)
            $ foldl (\ ma b -> case ma of
                      Just a -> joinSublogics b a
                      Nothing -> Nothing) (Just $ head sls) $ tail sls

-- | Update the list of finder
updateFinder :: TreeView -> ListStore Finder -> G_sublogics -> IO ()
updateFinder view list sl = do
  old <- listStoreToList list
  ps <- getUsableProvers ProveCMDLautomatic sl logicGraph
  let new = Map.elems $ foldr (\ (pr, c) m ->
              let n = getProverName pr
                  f = Map.findWithDefault (Finder n pr [] 0) n m
              in Map.insert n (f { comorphism = c : comorphism f}) m) Map.empty
              ps
  when (old /= new) $ do
    -- update list and try to select previous finder
    selected' <- getSelectedSingle view list
    sel <- treeViewGetSelection view
    listStoreClear list
    mapM_ (listStoreAppend list) $ mergeFinder old new
    maybe (selectFirst view)
      (\ (_, f) -> let i = findIndex ((fName f ==) . fName) new in
        maybe (selectFirst view) (treeSelectionSelectPath sel . (: [])) i
      ) selected'

-- | Try to select previous selected comorphism if possible
mergeFinder :: [Finder] -> [Finder] -> [Finder]
mergeFinder old new = let m' = Map.fromList $ map (\ f -> (fName f, f)) new in
  Map.elems $ foldl (\ m (Finder { fName = n, comorphism = cc, selected = i}) ->
      case Map.lookup n m of
        Nothing -> m
        Just f@(Finder { comorphism = cc' }) -> let c = cc !! i in
          Map.insert n (f { selected = fromMaybe 0 $ elemIndex c cc' }) m
    ) m' old

updateComorphism :: TreeView -> ListStore Finder -> ComboBox
                 -> ConnectId ComboBox -> IO ()
updateComorphism view list cbComorphism sh = do
  signalBlock sh
  model <- comboBoxGetModelText cbComorphism
  listStoreClear model
  mfinder <- getSelectedSingle view list
  case mfinder of
    Just (_, f) -> do
      mapM_ (comboBoxAppendText cbComorphism) $ expand f
      comboBoxSetActive cbComorphism $ selected f
    Nothing -> return ()
  signalUnblock sh

expand :: Finder -> [ComboBoxText]
expand = toComboBoxText . comorphism

setSelectedComorphism :: TreeView -> ListStore Finder -> ComboBox -> IO ()
setSelectedComorphism view list cbComorphism = do
  mfinder <- getSelectedSingle view list
  case mfinder of
    Just (i, f) -> do
      sel <- comboBoxGetActive cbComorphism
      listStoreSetValue list i f { selected = sel }
    Nothing -> return ()

-- | Displays the model view window
showModelViewAux :: MVar (IO ()) -> String -> ListStore FNode -> [FNode]
                 -> IO ()
showModelViewAux lock title list other = do
  builder <- getGTKBuilder ConsistencyChecker.get
  -- get objects
  window <- builderGetObject builder castToWindow "ModelView"
  btnClose <- builderGetObject builder castToButton "btnResClose"
  frNodes <- builderGetObject builder castToFrame "frResNodes"
  trvNodes <- builderGetObject builder castToTreeView "trvResNodes"
  tvModel <- builderGetObject builder castToTextView "tvResModel"

  windowSetTitle window title

  -- setup text view
  buffer <- textViewGetBuffer tvModel
  textBufferInsertAtCursor buffer ""

  tagTable <- textBufferGetTagTable buffer
  font <- textTagNew Nothing
  set font [ textTagFont := "FreeMono" ]
  textTagTableAdd tagTable font
  start <- textBufferGetStartIter buffer
  end <- textBufferGetEndIter buffer
  textBufferApplyTag buffer font start end

  -- setup list view
  let filterNodes = id

  nodes <- listStoreToList list
  listNodes <- setListData trvNodes show $ sort $ filterNodes $ other ++ nodes

  setListSelectorSingle trvNodes $ do
    mn <- getSelectedSingle trvNodes listNodes
    case mn of
      Nothing -> textBufferSetText buffer ""
      Just (_, n) -> textBufferSetText buffer $ showStatus n

  -- setup actions
  onClicked btnClose $ widgetDestroy window
  onDestroy window $ takeMVar lock >>= const (return ())

  putMVar lock $ do
    sel' <- getSelectedSingle trvNodes listNodes
    sel <- treeViewGetSelection trvNodes
    nodes'' <- listStoreToList list
    let nodes' = sort $ filterNodes nodes''
    updateListData listNodes $ sort (other ++ nodes')
    maybe (selectFirst trvNodes) (treeSelectionSelectPath sel . (: []))
      $ maybe Nothing (\ (_, n) -> findIndex ((name n ==) . name) nodes') sel'

  selectFirst trvNodes

  widgetSetSizeRequest window 800 600
  widgetSetSizeRequest frNodes 250 (-1)

  widgetShow window

-- | Displays the model view window
showModelView :: MVar (IO ()) -> String -> ListStore FNode -> [FNode] -> IO ()
showModelView lock title list other = do
  isNotOpen <- isEmptyMVar lock
  if isNotOpen then showModelViewAux lock title list other
    else join (readMVar lock)
