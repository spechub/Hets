{- |
Module      :  $Header$
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
import Graphics.UI.Gtk.Glade

import GUI.GtkUtils as GtkUtils
import qualified GUI.Glade.NodeChecker as ConsistencyChecker
import GUI.GraphTypes

import Static.DevGraph
import Static.PrintDevGraph ()
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Interfaces.GenericATPState (guiDefaultTimeLimit)

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism (..), hasModelExpansion)
import Logic.Prover

import Comorphisms.LogicGraph (logicGraph)
import Comorphisms.KnownProvers

import qualified Common.OrderedMap as OMap
import Common.AS_Annotation (isAxiom)
import Common.LibName (LibName)
import Common.Result

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.MVar
import Control.Monad (foldM_, join, when)

import Proofs.AbstractState

import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List
import Data.Maybe

-- | Data structure for saving the user-selected prover and comorphism
data Finder = Finder { fName      :: String
                     , finder     :: G_prover
                     , comorphism :: [AnyComorphism]
                     , selected   :: Int }

instance Eq Finder where
  f1 == f2 = fName f1 == fName f2 && comorphism f1 == comorphism f2

-- | stores each node to be considered along with some further infomation
data FNode = FNode { name     :: String
                   , node     :: LNode DGNodeLab
                   , sublogic :: G_sublogics
                   , goals    :: [String]
                     -- after proving, a new GTheory with the new Proofstatus
                     -- is computed
                   , results  :: G_theory }

-- | mostly for the purpose of proper display, the resulting G_theory of each
-- FNode can be converted into a list of Goals ( GtkUtils.Goal ).
toGtkGoals :: FNode -> [Goal]
toGtkGoals fn = case results fn of
  G_theory _ _ _ sens _ ->
    let sens' = OMap.filter (not . isAxiom) sens
        in foldr (\ s t -> case OMap.lookup s sens' of
                     Nothing -> t
                     Just tm -> case thmStatus tm of
                                  [] -> Goal GOpen s : t
                                  l -> Goal (GtkUtils.basicProofToGStatus
                                       (maximum $ map snd l)) s : t
                 ) [] $ goals fn

-- | as a Prefix for display purpose, the ratio of proven and total goals
-- is shown
goalsToPrefix :: [Goal] -> String
goalsToPrefix gs = let p = length $ filter (\ g -> gStatus g == GProved) gs
                   in "[" ++ show p ++ "/" ++ show (length gs) ++ "] "

-- | Displays every goal of a Node with a prefix showing the status and the
-- goal name.
showStatus :: FNode -> String
showStatus fn = intercalate "\n" . map (\ g -> GtkUtils.statusToPrefix
                 (gStatus g) ++ show (gName g)) $ toGtkGoals fn

-- | Get a markup string containing name and color
instance Show FNode where
  show fn = let gs = toGtkGoals fn
                gmin = gStatus $ minimum gs
            in
    "<span color=\"" ++ GtkUtils.statusToColor gmin ++ "\">"
     ++ goalsToPrefix gs ++ name fn ++ "</span>"

instance Eq FNode where
  (==) f1 f2 = compare f1 f2 == EQ

-- | for comparison, the goal status of each node is considered. only with
-- equal goal status, nodes are sorted by name.
instance Ord FNode where
  compare f1 f2 = let gmin f = minimum $ toGtkGoals f
            in case compare (gmin f1) (gmin f2) of
                 EQ -> compare (name f1) (name f2)
                 c  -> c

-- | gets all Nodes from the DGraph as input and creates a list of FNodes only
-- containing Nodes to be considered.
-- The results status field is initialised with the nodes local theory
initFNodes :: [LNode DGNodeLab] -> [FNode]
initFNodes = foldr (\ n@(_, l) t -> case globalTheory l of
                      Nothing -> t
                      Just gt ->
                        let gt' = dgn_theory l
                            gs = case gt' of
                                   G_theory _ _ _ s _ ->
                                     OMap.keys $ OMap.filter (not . isAxiom) s
                        in if null gs then t else
                       (FNode (getDGNodeName l) n (sublogicOfTh gt) gs gt') : t
              ) []

-- | returns True if a node has not been proved jet
unchecked :: FNode -> Bool
unchecked fn = case results fn of
                 G_theory _ _ _ sens _ ->
                   all null $ map thmStatus $ OMap.elems
                            $ OMap.filter (not . isAxiom) sens

-- | returns True if at least one goal has been timed out
timedout :: FNode -> Bool
timedout fn = any (\ a -> gStatus a == GTimeout) $ toGtkGoals fn

-- | returns True only if every goal has been proved
allProved :: FNode -> Bool
allProved fn = all (\ a -> gStatus a == GProved) $ toGtkGoals fn


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
  -- btnFineGrained    <- xmlGetWidget xml castToButton "btnFineGrained"
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

  toggleButtonSetActive cbInclThms False

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  threadId <- newEmptyMVar
  wait     <- newEmptyMVar
  mView    <- newEmptyMVar

  let dg    = lookupDGraph ln le
      nodes = initFNodes $ labNodesDG dg

  -- setup data
  listNodes  <- setListData trvNodes show $ sort nodes
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
                updateFinder  trvFinder listFinder s )
              (do
                labelSetLabel lblSublogic "No sublogic"
                listStoreClear listFinder
                activate widgets False
                widgetSetSensitive btnCheck False)
              (activate widgets True >> widgetSetSensitive btnCheck True)

  shN <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
    btnNodesInvert upd

  -- bindings

  -- this function handles the selction of nodes, getting as input parameter
  -- a function f (FNode -> Bool).
  let selectWith f u = do
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
      performAutoProof inclThms timeout prgBar f listNodes nodes'
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

  -- after window is closed, the results are written back into the DGraph.
  -- for each node a DGChange object is created and applied to the DGraph.
  onDestroy window $ do
    nodes' <- listStoreToList listNodes
    let dg' = foldl (\ cs fn ->
                      -- where the proving did not return anything, the node is
                      -- not updated
                      if unchecked fn then cs
                        else let
                          (i, l) = node fn
                          l' = l {dgn_theory = results fn}
                          n = (i, l' { globalTheory = computeLabelTheory
                                                           le dg (i, l') })
                          dg0 = changeDGH cs $ SetNodeLab l n
                          dg1 = togglePending dg0 $ changedLocalTheorems dg0 n
                          dg2 = togglePending dg1 $ changedPendingEdges dg1
                        in dg2 ) dg nodes'

    putMVar res $ Map.insert ln (groupHistory dg (DGRule "autoproof") dg') le

  -- setting up the selected items at startup
  selectWith (not . allProved) upd

  -- TODO select SPASS Prover if possible
  widgetShow window


performAutoProof :: -- include proven Theorems in subsequent proofs
                     Bool
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
                    -- no return value, since results are stored by changing
                    -- FNode data
                  -> IO ()
performAutoProof inclThms timeout update (Finder _ pr cs i) listNodes nodes =
  let count' = fromIntegral $ length nodes
      c = cs !! i
  in foldM_ (\ count (row, fn) -> do
           postGUISync $ update (count / count') $ name fn
           res <- autoProofAtNode inclThms timeout (node fn) (pr, c)
           case res of
             Just gt -> postGUISync $ listStoreSetValue listNodes row
               fn { results = propagateProofs (results fn) gt }
             Nothing -> return ()
           return $ count + 1) 0 nodes

autoProofAtNode :: -- use theorems is subsequent proofs
                    Bool
                   -- Timeout Limit
                  -> Int
                   -- Node selected for proving
                  -> LNode DGNodeLab
                   -- selected Prover and Comorphism
                  -> ( G_prover, AnyComorphism )
                   -- returns new GoalStatus for the Node
                  -> IO (Maybe G_theory)
autoProofAtNode useTh timeout (_, l) p_cm =
  case globalTheory l of
    Nothing -> return Nothing

    Just g_th@( G_theory lid _ _ _ _ ) -> do
      -- recompute the theory (to make effective the selected axioms, goals)
      let knpr = propagateErrors "autoProofAtNode"
            $ knownProversWithKind ProveCMDLautomatic
      pf_st <- initialState lid "" g_th knpr [p_cm]
      let st = recalculateSublogicAndSelectedTheory pf_st
      -- try to prepare the theory
      case maybeResult $ prepareForProving st p_cm of
        Nothing -> return Nothing

        Just (G_theory_with_prover lid1 th p) ->
          case proveCMDLautomaticBatch p of
            Nothing -> return Nothing

            Just fn -> do
              -- mVar to poll the prover for results
              answ <- newMVar (return [])
              (_, mV) <- fn useTh False answ (theoryName st)
                                       (TacticScript $ show timeout) th []
              takeMVar mV
              d <- takeMVar answ
              return $ case maybeResult d of
                Nothing -> Nothing
                Just d' ->
                  let ps' = markProved (snd p_cm) lid1 d' st
                  in case theory ps' of
                    G_theory lidT sigT indT sensT _ ->
                      case coerceThSens (logicId ps') lidT "" (goalMap ps') of
                        Nothing -> Nothing

                        Just gMap -> Just $
                          G_theory lidT sigT indT (Map.union sensT gMap)
                                   startThId

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
  let new = Map.elems $ foldr (\ (pr, c) m ->
              let n = getPName pr
                  f = Map.findWithDefault (Finder n pr [] 0) n m
              in Map.insert n (f { comorphism = c : comorphism f}) m) Map.empty
              $ getProvers ProveCMDLautomatic (Just sl)
              $ filter hasModelExpansion
              $ findComorphismPaths logicGraph sl
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
