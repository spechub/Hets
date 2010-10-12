{- |
Module      :  $Header$
Description :  Gtk GUI for the consistency checker
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the consistency checker.
-}

module GUI.GtkConsistencyChecker where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils
import qualified GUI.Glade.NodeChecker as ConsistencyChecker
import GUI.GraphTypes

import Static.DevGraph
import Static.PrintDevGraph ()
import Static.GTheory
import Static.History

import Interfaces.GenericATPState (guiDefaultTimeLimit)

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism (..))
import Logic.Prover

import Comorphisms.LogicGraph (logicGraph)

import Common.DocUtils
import Common.LibName (LibName)
import Common.Result
import Common.Consistency

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Monad (foldM_, join, when)

import Proofs.AbstractState
import Proofs.ConsistencyCheck

import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List (findIndex, partition, sort)
import Data.Maybe

data Finder = Finder { fName :: String
                     , finder :: G_cons_checker
                     , comorphism :: [AnyComorphism]
                     , selected :: Int }

instance Eq Finder where
  (==) (Finder { fName = n1, comorphism = c1 })
       (Finder { fName = n2, comorphism = c2 }) = n1 == n2 && c1 == c2

data FNode = FNode { name :: String
                   , node :: LNode DGNodeLab
                   , sublogic :: G_sublogics
                   , cStatus :: ConsistencyStatus }

-- | Get a markup string containing name and color
instance Show FNode where
  show FNode { name = n, cStatus = s } =
    "<span color=\"" ++ cStatusToColor s ++ "\">" ++ cStatusToPrefix s ++ n ++
    "</span>"

instance Eq FNode where
  (==) f1 f2 = compare f1 f2 == EQ

instance Ord FNode where
  compare (FNode { name = n1, cStatus = s1 })
          (FNode { name = n2, cStatus = s2 }) = case compare s1 s2 of
    EQ -> compare n1 n2
    c -> c

cStatusToColor :: ConsistencyStatus -> String
cStatusToColor s = case sType s of
  CSUnchecked -> "black"
  CSConsistent -> "green"
  CSInconsistent -> "red"
  CSDisproved -> "orange"
  CSTimeout -> "blue"
  CSError -> "darkred"

cStatusToPrefix :: ConsistencyStatus -> String
cStatusToPrefix s = case sType s of
  CSUnchecked -> "[ ] "
  CSConsistent -> "[+] "
  CSInconsistent -> "[-] "
  CSDisproved -> "[d] "
  CSTimeout -> "[t] "
  CSError -> "[f] "

-- | Displays the consistency checker window
showConsistencyChecker :: Maybe Int -> GInfo -> LibEnv -> IO (Result LibEnv)
showConsistencyChecker mn gi@(GInfo { libName = ln }) le =
  case mn of
    Nothing -> showConsistencyCheckerMain mn gi le
    Just n -> let
      dg = lookupDGraph ln le
      lbl = labDG dg n
      in if case globalTheory lbl of
        Just (G_theory _ _ _ sens _) -> Map.null sens
        Nothing -> True
        then do
          infoDialog "No sentences" $ "Node " ++
            getDGNodeName lbl
            ++ " has no sentences and is thus trivially consistent"
          return $ return le
        else showConsistencyCheckerMain mn gi le

-- | Displays the consistency checker window
showConsistencyCheckerMain :: Maybe Int -> GInfo -> LibEnv -> IO (Result LibEnv)
showConsistencyCheckerMain mn (GInfo { libName = ln }) le = do
  wait <- newEmptyMVar
  showConsistencyCheckerAux wait mn ln le
  le' <- takeMVar wait
  return $ Result [] $ Just le'

-- | Displays the consistency checker window
showConsistencyCheckerAux
  :: MVar LibEnv -> Maybe Int -> LibName -> LibEnv -> IO ()
showConsistencyCheckerAux res mn ln le = postGUIAsync $ do
  xml <- getGladeXML ConsistencyChecker.get
  -- get objects
  window <- xmlGetWidget xml castToWindow "NodeChecker"
  btnClose <- xmlGetWidget xml castToButton "btnClose"
  btnResults <- xmlGetWidget xml castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout <- xmlGetWidget xml castToButton "btnNodesTimeout"
  cbInclThms <- xmlGetWidget xml castToCheckButton "cbInclThms"
  -- get checker view and buttons
  cbComorphism <- xmlGetWidget xml castToComboBox "cbComorphism"
  lblSublogic <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck <- xmlGetWidget xml castToButton "btnCheck"
  btnStop <- xmlGetWidget xml castToButton "btnStop"
  trvFinder <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"
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

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait <- newEmptyMVar
  mView <- newEmptyMVar

  let dg = lookupDGraph ln le
      nodes = labNodesDG dg
      selNodes = partition (\ (FNode { node = (_, l)}) -> case globalTheory l of
        Just (G_theory _ _ _ sens _) -> Map.null sens
        Nothing -> True)
      sls = map sublogicOfTh $ mapMaybe (globalTheory . snd) nodes

      n2CS n = case getNodeConsStatus n of
                 ConsStatus _ pc thmls ->
                   let t = showDoc thmls "" in case pc of
                   Inconsistent -> ConsistencyStatus CSInconsistent t
                   Cons -> ConsistencyStatus CSConsistent t
                   _ -> ConsistencyStatus CSUnchecked t
      (emptyNodes, others) = selNodes
        $ map (\ (n@(_, l), s) -> FNode (getDGNodeName l) n s $ n2CS l)
        $ zip nodes sls

  -- setup data
  listNodes <- setListData trvNodes show $ sort others
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
        (\ b s -> do
           labelSetLabel lblSublogic $ show s
           updateFinder trvFinder listFinder b s)
        (do
          labelSetLabel lblSublogic "No sublogic"
          listStoreClear listFinder
          activate widgets False
          widgetSetSensitive btnCheck False)
        (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings
  let selectWithAux f u = do
        signalBlock shN
        sel <- treeViewGetSelection trvNodes
        treeSelectionSelectAll sel
        rs <- treeSelectionGetSelectedRows sel
        mapM_ ( \ p@(row : []) -> do
          fn <- listStoreGetValue listNodes row
          (if f fn then treeSelectionSelectPath else treeSelectionUnselectPath)
            sel p) rs
        signalUnblock shN
        u
      selectWith f = selectWithAux $ f . cStatus

  onClicked btnNodesUnchecked
    $ selectWith (== ConsistencyStatus CSUnchecked "") upd
  onClicked btnNodesTimeout $ selectWith (== ConsistencyStatus CSTimeout "") upd

  onClicked btnResults $ showModelView mView "Models" listNodes emptyNodes
  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    inclThms <- toggleButtonGetActive cbInclThms
    (updat, pexit) <- progressBar "Checking consistency" "please wait..."
    nodes' <- getSelectedMultiple trvNodes listNodes
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Consistency checker: internal error"
      Just (_, f) -> return f
    switch False
    tid <- forkIO $ do
      check False inclThms ln le dg f timeout listNodes updat nodes'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of consistency check" listNodes emptyNodes
        signalBlock shN
        sortNodes trvNodes listNodes
        signalUnblock shN
        upd
        activate checkWidgets True
        pexit

  onDestroy window $ do
    nodes' <- listStoreToList listNodes
    let changes = foldl (\ cs (FNode { node = (i, l), cStatus = s }) ->
                      if (\ st -> st /= CSConsistent && st /= CSInconsistent)
                         $ sType s then cs
                        else
                          let n = (i, if sType s == CSInconsistent then
                                        markNodeInconsistent "" l
                                        else markNodeConsistent "" l)
                          in SetNodeLab l n : cs
                    ) [] nodes'
        dg' = changesDGH dg changes
    putMVar res $ Map.insert ln (groupHistory dg (DGRule "Consistency") dg') le

  selectWithAux (maybe ((== ConsistencyStatus CSUnchecked "") . cStatus)
          (\ n -> (== n) . fst . node) mn) upd
  widgetShow window

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
updateNodes :: TreeView -> ListStore FNode -> (Bool -> G_sublogics -> IO ())
            -> IO () -> IO () -> IO ()
updateNodes view listNodes update lock unlock = do
  nodes <- getSelectedMultiple view listNodes
  if null nodes then lock
    else let sls = map (sublogic . snd) nodes in
      maybe lock (\ sl -> unlock >> update (length nodes == 1) sl)
            $ foldl (\ ma b -> case ma of
                      Just a -> joinSublogics b a
                      Nothing -> Nothing) (Just $ head sls) $ tail sls

-- | Update the list of finder
updateFinder :: TreeView -> ListStore Finder -> Bool -> G_sublogics -> IO ()
updateFinder view list useNonBatch sl = do
  old <- listStoreToList list
  let new = Map.elems $ foldr (\ (cc, c) m ->
              let n = getPName cc
                  f = Map.findWithDefault (Finder n cc [] 0) n m
              in Map.insert n (f { comorphism = c : comorphism f}) m) Map.empty
              $ filter (\ (G_cons_checker _ cc, _) -> useNonBatch || ccBatch cc)
              $ getConsCheckers $ findComorphismPaths logicGraph sl
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
          Map.insert n (f { selected = fromMaybe 0 $ findIndex (== c) cc' }) m
    ) m' old

check :: Bool -> Bool -> LibName -> LibEnv -> DGraph -> Finder -> Int
      -> ListStore FNode -> (Double -> String -> IO ()) -> [(Int, FNode)]
      -> IO ()
check dispr inclThms ln le dg (Finder _ cc cs i) timeout listNodes update
  nodes = let
    count' = fromIntegral $ length nodes
    c = cs !! i in
  foldM_ (\ count (row, fn@(FNode { name = n', node = n })) -> do
           postGUISync $ update (count / count') n'
           res <- consistencyCheck inclThms cc c ln le dg n timeout
           let res' = case dispr && (sType res) == CSConsistent of
                        True -> ConsistencyStatus CSDisproved (sMessage res)
                        False -> res
           postGUISync $ listStoreSetValue listNodes row fn { cStatus = res' }
           return $ count + 1) 0 nodes

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

expand :: Finder -> [String]
expand = map show . comorphism

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
  xml <- getGladeXML ConsistencyChecker.get
  -- get objects
  window <- xmlGetWidget xml castToWindow "ModelView"
  btnClose <- xmlGetWidget xml castToButton "btnResClose"
  frNodes <- xmlGetWidget xml castToFrame "frResNodes"
  trvNodes <- xmlGetWidget xml castToTreeView "trvResNodes"
  tvModel <- xmlGetWidget xml castToTextView "tvResModel"

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
  let filterNodes = filter ((/= ConsistencyStatus CSUnchecked "") . cStatus)

  nodes <- listStoreToList list
  listNodes <- setListData trvNodes show $ sort $ filterNodes $ other ++ nodes

  setListSelectorSingle trvNodes $ do
    mn <- getSelectedSingle trvNodes listNodes
    case mn of
      Nothing -> textBufferSetText buffer ""
      Just (_, n) -> textBufferSetText buffer $ show $ cStatus n

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
