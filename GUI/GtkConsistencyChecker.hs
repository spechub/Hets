{- |
Module      :  $Header$
Description :  Gtk GUI for the consistency checker
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

This module provides a GUI for the consistency checker.
-}

module GUI.GtkConsistencyChecker
  (showConsistencyChecker)
  where

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade
import Graphics.UI.Gtk.ModelView as MV

import GUI.GtkUtils
import qualified GUI.Glade.ConsistencyChecker as ConsistencyChecker
import GUI.GraphTypes

import Static.DevGraph
import Static.GTheory

import Interfaces.DataTypes

import Logic.Logic (Language(language_name))
import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism(..))

import Comorphisms.LogicGraph (logicGraph)

import Common.LibName (LibName)

import Control.Concurrent.MVar
import Control.Monad (foldM, join, mapM_)

import Proofs.AbstractState
import Proofs.InferBasic (consistencyCheck, ConsistencyStatus (..))

import Data.IORef
import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List (findIndex)
import Data.Maybe

data Finder = Finder { fname :: String
                     , finder :: G_cons_checker
                     , comorphs :: [AnyComorphism]
                     , selected :: Int }

data FNode = FNode { name :: String
                   , node :: LNode DGNodeLab
                   , sublogic :: G_sublogics
                   , status :: ConsistencyStatus }

instance Show ConsistencyStatus where
  show CSUnchecked = "Unchecked"
  show (CSConsistent s) = s
  show (CSInconsistent s) = s
  show (CSTimeout s) = s
  show (CSError s) = s

instance Eq ConsistencyStatus where
  (==) CSUnchecked CSUnchecked = True
  (==) (CSConsistent _) (CSConsistent _) = True
  (==) (CSInconsistent _) (CSInconsistent _) = True
  (==) (CSTimeout _) (CSTimeout _) = True
  (==) (CSError _) (CSError _) = True
  (==) _ _ = False

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> IO ()
showConsistencyChecker gInfo@(GInfo { libName = ln }) = postGUIAsync $ do
  xml               <- getGladeXML ConsistencyChecker.get
  -- get objects
  window            <- xmlGetWidget xml castToWindow "ConsistencyChecker"
  btnClose          <- xmlGetWidget xml castToButton "btnClose"
  btnResults         <- xmlGetWidget xml castToButton "btnResults"
  -- get nodes view and buttons
  trvNodes          <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll       <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone      <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert    <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout   <- xmlGetWidget xml castToButton "btnNodesTimeout"
  -- get checker view and buttons
  lblComorphism     <- xmlGetWidget xml castToLabel "lblComorphism"
  lblSublogic       <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout         <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck          <- xmlGetWidget xml castToButton "btnCheck"
  btnStop           <- xmlGetWidget xml castToButton "btnStop"
  btnFineGrained    <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder         <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"

  let widgets = [ toWidget trvFinder
                , toWidget btnFineGrained
                , toWidget sbTimeout
                , toWidget lblComorphism
                , toWidget lblSublogic
                ]
      checkWidgets = widgets ++ [ toWidget btnClose
                                , toWidget trvNodes
                                , toWidget btnNodesAll
                                , toWidget btnNodesNone
                                , toWidget btnNodesInvert
                                , toWidget btnNodesUnchecked
                                , toWidget btnNodesTimeout
                                , toWidget btnResults
                                ]
      switch b = do
        widgetSetSensitive btnStop $ not b
        widgetSetSensitive btnCheck b

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False
  widgetSetSensitive btnResults False

  stop <- newEmptyMVar
  mView <- newEmptyMVar

  -- get nodes
  (le, dg, nodes) <- do
    ost <- readIORef $ intState gInfo
    case i_state ost of
      Nothing -> error "No state given."
      Just ist -> do
        let le = i_libEnv ist
            dg = lookupDGraph ln le
        return (le, dg, labNodesDG dg)
  let sls = map sublogicOfTh $ mapMaybe (globalTheory . snd) nodes

  -- setup data
  listNodes <- setListData trvNodes getFNodeName
    $ map (\ (n@(_,l),s) -> FNode (getDGNodeName l) n s CSUnchecked)
    $ zip nodes sls
  listFinder <- setListData trvFinder fname []

  -- setup view selection actions
  let update = do mf <- getSelectedSingle trvFinder listFinder
                  case mf of
                    Just (_,f) -> do
                      case comorphs f !! selected f of
                        Comorphism cid ->
                          let cName = language_name cid
                              dName = drop 1 $ dropWhile (/= ';') cName
                          in labelSetLabel lblComorphism
                            $ if null dName then "identity" else dName
                      widgetSetSensitive btnCheck True
                    Nothing -> do
                      labelSetLabel lblComorphism "No path selected"
                      widgetSetSensitive btnCheck False
  setListSelectorSingle trvFinder update

  selection <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
                 btnNodesInvert $ updateNodes trvNodes listNodes
                                    (\ s -> do
                                       labelSetLabel lblSublogic $ show s
                                       updateFinder trvFinder listFinder s)
                                    (do labelSetLabel lblSublogic "No sublogic"
                                        listStoreClear listFinder
                                        activate widgets False
                                        widgetSetSensitive btnCheck False)
                                    (do activate widgets True
                                        widgetSetSensitive btnCheck False)

  -- bindings
  let selectWith f = do
        mModel <- treeViewGetModel trvNodes
        case mModel of
          Nothing -> return ()
          Just m -> do
            writeIORef selection []
            selector <- treeViewGetSelection trvNodes
            treeModelForeach m $ \ iter -> do
              path@(row:[]) <- treeModelGetPath m iter
              (FNode { status = s }) <- listStoreGetValue listNodes row
              if f s then do
                  treeSelectionSelectIter selector iter
                  modifyIORef selection (path:)
                else treeSelectionUnselectIter selector iter
              return False

  onClicked btnNodesUnchecked $ selectWith (== CSUnchecked)
  onClicked btnNodesTimeout  $ selectWith (== CSTimeout "")

  onClicked btnResults $ showModelView mView "Models" listNodes
  onClicked btnClose $ widgetDestroy window
  onClicked btnFineGrained $ fineGrainedSelection trvFinder listFinder update
  onClicked btnStop $ do
    mStopF <- tryTakeMVar stop
    case mStopF of
      Nothing -> return ()
      Just stopF -> stopF

  onClicked btnCheck $ do
    activate checkWidgets False
    timeout <- spinButtonGetValueAsInt sbTimeout
    (updat, exit) <- progressBar "Checking consistency" "please wait..."
    nodes' <- getSelectedMultiple trvNodes listNodes
    mf <- getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Consistency checker: internal error"
      Just (_,f) -> return f
    switch False
    forkIOWithPostProcessing
      (check ln le dg f timeout updat nodes' stop)
      $ \ res -> do
        widgetSetSensitive btnStop False
        mapM_ (uncurry (listStoreSetValue listNodes)) res
        tryTakeMVar stop
        switch True
        showModelView mView "Results of consistency check" listNodes
        activate checkWidgets True
        exit

  widgetShow window

statusToColor :: ConsistencyStatus -> String
statusToColor s = case s of
  CSUnchecked -> "black"
  CSConsistent _ -> "green"
  CSInconsistent _ -> "red"
  CSTimeout _ -> "blue"
  CSError _ -> "darkred"

statusToPrefix :: ConsistencyStatus -> String
statusToPrefix s = case s of
  CSUnchecked -> "[?] "
  CSConsistent _ -> "[+] "
  CSInconsistent _ -> "[-] "
  CSTimeout _ -> "[t] "
  CSError _ -> "[f] "

-- | Get a markup string containing name and color
getFNodeName :: FNode -> String
getFNodeName (FNode { name = n, status = s }) =
  "<span color=\"" ++ statusToColor s ++ "\">" ++ statusToPrefix s ++ n ++
  "</span>"

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore FNode -> (G_sublogics -> IO ())
            -> IO () -> IO () -> IO ()
updateNodes view listNodes update lock unlock = do
  nodes <- getSelectedMultiple view listNodes
  if null nodes then lock
    else let sls = map (sublogic . snd) nodes in
      maybe lock (\ sl -> do unlock; update sl)
            $ foldl (\ ma b -> case ma of
                      Just a -> joinSublogics b a
                      Nothing -> Nothing) (Just $ head sls) $ tail sls

-- | Update the list of finder
updateFinder :: TreeView -> ListStore Finder -> G_sublogics -> IO ()
updateFinder view list sl = do
  (update, exit) <- pulseBar "Calculating paths" "please wait..."
  listStoreClear list
  forkIOWithPostProcessing
    (return $ Map.elems $ foldr
                (\ (cc, c) m ->
                  let n = getPName cc
                      f = Map.findWithDefault (Finder n cc [] 0) n m in
                  Map.insert n (f { comorphs = c : comorphs f}) m
                ) Map.empty
                $ getConsCheckers $ findComorphismPaths logicGraph sl)
    $ \ res -> do
      mapM_ (listStoreAppend list) res
      update "finished"
      exit
      selectFirst view

activate :: [Widget] -> Bool -> IO ()
activate widgets active = mapM_ (\ w -> widgetSetSensitive w active) widgets

check :: LibName -> LibEnv -> DGraph -> Finder -> Int
      -> (Double -> String -> IO ()) -> [(Int,FNode)] -> MVar (IO ())
      -> IO [(Int, FNode)]
check ln le dg (Finder { finder = cc, comorphs = cs, selected = i}) timeout
      update nodes stop = do
  stop' <- newEmptyMVar
  putMVar stop $ putMVar stop' ()
  let count' = fromIntegral $ length nodes
      c = cs !! i
  (_,r) <- foldM (\ (count, r) (row, fn@(FNode { name = n', node = n })) -> do
                   run <- isEmptyMVar stop'
                   r' <- if run then do
                       postGUISync $ update (count / count') n'
                       res <- consistencyCheck cc c ln le dg n timeout
                       return $ (row, fn { status = res }):r
                     else return r
                   return (count+1, r')) (0,[]) nodes
  return r

fineGrainedSelection :: TreeView -> ListStore Finder -> IO () -> IO ()
fineGrainedSelection view list unlock = do
  paths <- listStoreToList list
  selector <- treeViewGetSelection view
  if null paths then error "Cant make selection without sublogic!"
    else do
      ret <- listChoiceAux "Choose a translation"
               (\ (n,_,c) -> n ++ ": " ++ show c) $ concatMap expand paths
      case ret of
        Just (_,(n,_,c)) -> case findIndex ((n ==) . fname) paths of
          Just i -> let f = paths !! i in case findIndex (c ==) $ comorphs f of
            Just i' -> do
              listStoreSetValue list i $ f { selected = i' }
              treeSelectionSelectPath selector [i]
              unlock
            Nothing -> return ()
          Nothing -> return ()
        Nothing -> return ()

expand :: Finder -> [(String, G_cons_checker, AnyComorphism)]
expand (Finder { fname = n, finder = cc, comorphs = cs }) =
  map (\ c -> (n,cc,c)) cs

-- | Displays the model view window
showModelViewAux :: MVar (IO ()) -> String -> ListStore FNode -> IO ()
showModelViewAux lock title list = do
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
  let filterNodes = filter ((/= CSUnchecked) . status)

  nodes <- listStoreToList list
  listNodes <- setListData trvNodes getFNodeName $ filterNodes nodes

  setListSelectorSingle trvNodes $ do
    mn <- getSelectedSingle trvNodes listNodes
    case mn of
      Nothing -> textBufferSetText buffer ""
      Just (_,n) -> textBufferSetText buffer $ show $ status n


  -- setup actions
  onClicked btnClose $ widgetDestroy window
  onDestroy window $ do takeMVar lock; return ()

  putMVar lock $ do
    nodes' <- listStoreToList list
    updateListData listNodes $ filterNodes nodes'

  widgetSetSizeRequest window 800 600
  widgetSetSizeRequest frNodes 250 (-1)

  widgetShow window

-- | Displays the model view window
showModelView :: MVar (IO ()) -> String -> ListStore FNode -> IO ()
showModelView lock title list  = do
  isNotOpen <- isEmptyMVar lock
  if isNotOpen then showModelViewAux lock title list
    else join (readMVar lock)

