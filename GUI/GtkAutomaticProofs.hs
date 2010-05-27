{- |
Module      :  $Header$
Description :  Gtk GUI for the consistency checker
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the consistency checker.
-}

module GUI.GtkAutomaticProofs
  (showAutomaticProofs)
  where

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
import Interfaces.DataTypes
import Interfaces.Utils (updateNodeProof)

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism(..))
import Logic.Logic (language_name)
import Logic.Prover

import Comorphisms.LogicGraph (logicGraph)
import Comorphisms.KnownProvers

import Common.DocUtils
import Common.LibName (LibName)
import Common.Result
import Common.Consistency

import Control.Concurrent (ThreadId, forkIO, killThread)
import Control.Concurrent.MVar
import Control.Monad (foldM_, join, when)

import Proofs.AbstractState
import Proofs.InferBasic

import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List (findIndex, partition, sort)
import Data.Maybe

data Finder = Finder { fName      :: String
                     , finder     :: G_prover
                     , comorphism :: [AnyComorphism]
                     , selected   :: Int }

instance Eq Finder where
  f1 == f2 = fName f1 == fName f2 && comorphism f1 == comorphism f2

data FNode = FNode { name     :: String
                   , node     :: LNode DGNodeLab
                   , sublogic :: G_sublogics
                   , status   :: Bool } --ProofStatus' }

data ProofStatus' = Unchecked
                  | Proved_All
                  | Proved_Some
                  | Proved_None
                  | Timeout
                  | P_Error
                  deriving Eq

instance Show ProofStatus' where
  show ps = statusToPrefix ps ++ statusToColor ps

-- | does not make much sense, but needed some function for compare
instance Ord ProofStatus' where
  compare ps1 ps2 = compare (statusToColor ps1) (statusToColor ps2)

statusToColor :: ProofStatus' -> String
statusToColor ps = case ps of
  Unchecked    -> "black"
  Proved_All   -> "green"
  Proved_Some  -> "orange"
  Proved_None  -> "red"
  Timeout      -> "blue"
  P_Error      -> "darkred"

statusToPrefix :: ProofStatus' -> String
statusToPrefix ps = case ps of
  Unchecked    -> "[ ] "
  Proved_All   -> "[+] "
  Proved_Some  -> "[/] "
  Proved_None  -> "[-] "
  Timeout      -> "[t] "
  P_Error      -> "[f] "

-- | Get a markup string containing name and color
instance Show FNode where
  show fn =
    "<span color=\"" ++ "black" --statusToColor( status fn )
    ++ "\">" ++ "[] " ++ name fn ++ "</span>"

instance Eq FNode where
  (==) f1 f2 = compare f1 f2 == EQ

instance Ord FNode where
  compare (FNode { name = n1, status = s1 })
          (FNode { name = n2, status = s2 }) = case compare s1 s2 of
    EQ -> compare n1 n2
    c  -> c

-- | Displays the consistency checker window
showAutomaticProofs :: GInfo -> LibEnv -> IO (Result LibEnv)
showAutomaticProofs (GInfo { libName = ln }) le = do
  wait <- newEmptyMVar
  showProverWindow wait ln le
  le' <- takeMVar wait
  return $ Result [] $ Just le'

-- | Displays the consistency checker window
showProverWindow :: MVar LibEnv -> LibName -> LibEnv -> IO ()
showProverWindow res ln le = postGUIAsync $ do
  xml               <- getGladeXML ConsistencyChecker.get
  -- get objects
  window            <- xmlGetWidget xml castToWindow "NodeChecker"
  btnClose          <- xmlGetWidget xml castToButton "btnClose"
  btnResults         <- xmlGetWidget xml castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes          <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll       <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone      <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert    <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout   <- xmlGetWidget xml castToButton "btnNodesTimeout"
  cbInclThms        <- xmlGetWidget xml castToCheckButton "cbInclThms"
  -- get checker view and buttons
  cbComorphism      <- xmlGetWidget xml castToComboBox "cbComorphism"
  lblSublogic       <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout         <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck          <- xmlGetWidget xml castToButton "btnCheck"
  btnStop           <- xmlGetWidget xml castToButton "btnStop"
  --btnFineGrained    <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder         <- xmlGetWidget xml castToTreeView "trvFinder"

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

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait <- newEmptyMVar
  mView <- newEmptyMVar

  let dg = lookupDGraph ln le
      nodes = labNodesDG dg
      selNodes = partition (\ (FNode { node = (_,l)}) -> case globalTheory l of
        Just (G_theory _ _ _ sens _) -> Map.null sens
        Nothing -> True)
      sls = map sublogicOfTh $ mapMaybe (globalTheory . snd) nodes

      (emptyNodes, others) = selNodes
        $ map (\ (n@(_,l), s) -> FNode (getDGNodeName l) n s False)
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
        (\ b s -> do labelSetLabel lblSublogic $ show s
                     updateFinder trvFinder listFinder b s)
        (do labelSetLabel lblSublogic "No sublogic"
            listStoreClear listFinder
            activate widgets False
            widgetSetSensitive btnCheck False)
        (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings
  let selectWith f u = do
        signalBlock shN
        sel <- treeViewGetSelection trvNodes
        treeSelectionSelectAll sel
        rs <- treeSelectionGetSelectedRows sel
        mapM_ ( \ p@(row:[]) -> do
          (FNode { status = s }) <- listStoreGetValue listNodes row
          (if f s then treeSelectionSelectPath else treeSelectionUnselectPath)
            sel p) rs
        signalUnblock shN
        u

  onClicked btnNodesUnchecked
    $ selectWith ( const True ) upd
  onClicked btnNodesTimeout $ selectWith ( const False ) upd

  onClicked btnResults $ showModelView mView "Models" listNodes emptyNodes
  onClicked btnClose $ widgetDestroy window
  onClicked btnStop $ takeMVar threadId >>= killThread >>= putMVar wait

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    inclThms <- toggleButtonGetActive cbInclThms
    (updat, exit) <- progressBar "Proving" "please wait..."
    nodes' <- getSelectedMultiple trvNodes listNodes
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Automatic Proofs: internal error"
      Just (_,f) -> return f
    switch False
    tid <- forkIO $ do
      check inclThms ln le dg f timeout listNodes updat nodes'
      putMVar wait ()
    putMVar threadId tid
    forkIO_ $ do
      takeMVar wait
      postGUIAsync $ do
        switch True
        tryTakeMVar threadId
        showModelView mView "Results of automatic proofs" listNodes emptyNodes
        signalBlock shN
        sortNodes trvNodes listNodes
        signalUnblock shN
        upd
        activate checkWidgets True
        exit

  onDestroy window $ do
    nodes' <- listStoreToList listNodes
    let changes = foldl (\ cs fn ->
                      if status fn then cs
                        else
                          let n@(_, l) = node fn
                          in SetNodeLab l n : cs
                    ) [] nodes'
        dg' = changesDGH dg changes
    putMVar res $ Map.insert ln (groupHistory dg (DGRule "autoproof") dg') le

  selectWith not upd

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
  let new = Map.elems $ foldr (\ (pr, c) m ->
              let n = getPName pr
                  f = Map.findWithDefault (Finder n pr [] 0) n m
              in Map.insert n (f { comorphism = c : comorphism f}) m) Map.empty
              $ getProvers ProveCMDLautomatic (Just sl) $ findComorphismPaths logicGraph sl
  when (old /= new) $ do
    -- update list and try to select previous finder
    selected' <- getSelectedSingle view list
    sel <- treeViewGetSelection view
    listStoreClear list
    mapM_ (listStoreAppend list) $ mergeFinder old new
    maybe (selectFirst view)
      (\ (_,f) -> let i = findIndex ((fName f ==) . fName) new in
        maybe (selectFirst view) (treeSelectionSelectPath sel . (:[])) i
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

check :: Bool -> LibName -> LibEnv -> DGraph -> Finder -> Int -> ListStore FNode
      -> (Double -> String -> IO ()) -> [(Int,FNode)] -> IO ()
check inclThms ln le dg (Finder { finder = pr, comorphism = cs, selected = i})
  timeout listNodes update nodes = let
    count' = fromIntegral $ length nodes
    c = cs !! i in
  foldM_ (\ count (row, fn@(FNode { name = n', node = n })) -> do
           postGUISync $ update (count / count') n'
           res <- proveNode' inclThms timeout n (pr, c) ln
           -- res <- consistencyCheck inclThms cc c ln le dg n timeout
           putStrLn res
           postGUISync $ listStoreSetValue listNodes row fn { status = True }
           return $ count + 1) 0 nodes

-- | to look up the data types of the 'old' call from consistencyChecker, that need to be adjusted
-- | in order to match the data types requested in proveNode'
-- consistencyCheck :: Bool -> G_cons_checker -> AnyComorphism -> LibName -> LibEnv
--                 -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus

-- //////////////////////////////////////////////////////////////////////////
-- | inserted proveNode from CMDL/ProveConsistency and made some changes

-- | Given a proofstatus the function does the actual call of the
-- prover for proving the node or check consistency
proveNode' ::
              --use theorems is subsequent proofs
              Bool ->
              -- Timeout Limit
              Int ->

              LNode DGNodeLab ->
	      -- selected Prover and Comorphism
              ( G_prover, AnyComorphism ) ->
              -- MVar (Maybe ThreadId) ->
              -- MVar (Maybe Int_NodeInfo)  ->
              -- MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
               IO String
proveNode' useTh timeout lnode@(_, lab) p_cm@(_, acm) libname =
  case fromMaybe (error "GtkAutomaticProofs.proveNode': noG_theory") $ globalTheory lab of
    g_th@( G_theory lid _ _ _ _ ) -> do
      -- recompute the theory (to make effective the selected axioms,
      -- goals)
     let knpr = propagateErrors $ knownProversWithKind ProveCMDLautomatic
     pf_st <- initialState lid "" g_th knpr [p_cm] 
     let st = recalculateSublogicAndSelectedTheory pf_st
     -- try to prepare the theory
     prep <- case prepareForProving st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv',acm'@(Comorphism cid)) <-
                          lookupKnownProver st ProveCMDLautomatic
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using prover " ++ getPName prv')
                return $ case prepareForProving st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just (sm,acm')
             Result _ (Just sm) -> return $ Just (sm,acm)
     case prep of
     -- theory could not be computed
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_prover lid1 th p, cmp)->
        case proveCMDLautomaticBatch p of
         Nothing -> return "Error obtaining the prover"
         Just fn -> do
          -- mVar to poll the prover for results
          answ <- newMVar (return [])
          case selectedGoals st of
           [] -> return "No goals selected. Nothing to prove"
           _ -> do
             ( thrId, mV ) <- fn useTh
                              False
                              answ
                              (theoryName st)
                              (TacticScript $ show timeout)
                              th []
             -- mThr          <- newMVar $ Just thrId
             takeMVar mV
             return ""

-- | proveNode END
-- //////////////////////////////////////////////////////////

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
  xml      <- getGladeXML ConsistencyChecker.get
  -- get objects
  window   <- xmlGetWidget xml castToWindow "ModelView"
  btnClose <- xmlGetWidget xml castToButton "btnResClose"
  frNodes  <- xmlGetWidget xml castToFrame "frResNodes"
  trvNodes <- xmlGetWidget xml castToTreeView "trvResNodes"
  tvModel  <- xmlGetWidget xml castToTextView "tvResModel"

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
      Just (_,n) -> textBufferSetText buffer $ show $ status n

  -- setup actions
  onClicked btnClose $ widgetDestroy window
  onDestroy window $ takeMVar lock >>= const (return ())

  putMVar lock $ do
    sel' <- getSelectedSingle trvNodes listNodes
    sel <- treeViewGetSelection trvNodes
    nodes'' <- listStoreToList list
    let nodes' = sort $ filterNodes nodes''
    updateListData listNodes $ sort (other ++ nodes')
    maybe (selectFirst trvNodes) (treeSelectionSelectPath sel . (:[]))
      $ maybe Nothing (\ (_,n) -> findIndex ((name n ==) . name) nodes') sel'

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

