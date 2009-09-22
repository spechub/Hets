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
import Static.DGTranslation (comSublogics)

import Interfaces.DataTypes

import Logic.Grothendieck
import Logic.Comorphism (AnyComorphism)

import Comorphisms.LogicGraph (logicGraph)

import Common.LibName (LIB_NAME)
import Common.Result

import Control.Concurrent (forkIO, killThread, ThreadId)
import Control.Concurrent.MVar
import Control.Monad (foldM_, join, mapM_)

import Proofs.AbstractState
import Proofs.InferBasic (consistencyCheck)

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
                   , model :: Result G_theory}

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> IO ()
showConsistencyChecker gInfo@(GInfo { libName = ln }) = postGUIAsync $ do
  xml               <- getGladeXML ConsistencyChecker.get
  -- get objects
  window            <- xmlGetWidget xml castToWindow "ConsistencyChecker"
  btnClose          <- xmlGetWidget xml castToButton "btnClose"
  btnModels         <- xmlGetWidget xml castToButton "btnModels"
  -- get nodes view and buttons
  trvNodes          <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll       <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone      <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert    <- xmlGetWidget xml castToButton "btnNodesInvert"
  btnNodesUnchecked <- xmlGetWidget xml castToButton "btnNodesUnchecked"
  btnNodesTimeout   <- xmlGetWidget xml castToButton "btnNodesTimeout"
  -- get checker view and buttons
  lblStatus         <- xmlGetWidget xml castToLabel "lblStatus"
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
                , toWidget lblStatus
                , toWidget lblSublogic
                ]
      checkWidgets = widgets ++ [ toWidget btnClose
                                , toWidget trvNodes
                                , toWidget btnNodesAll
                                , toWidget btnNodesNone
                                , toWidget btnNodesInvert
                                , toWidget btnNodesUnchecked
                                , toWidget btnNodesTimeout
                                , toWidget btnModels
                                ]

  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  run <- newMVar Nothing
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
  ths <- mapM (\ (_,l) -> computeLocalLabelTheory le l) nodes
  let sls = map sublogicOfTh ths
      switch b = do
        widgetSetSensitive btnStop $ not b
        widgetSetSensitive btnCheck b

  -- setup data
  listNodes <- setListData trvNodes getFNodeName
                 $ map (\ (n@(_,l),s) -> FNode (getDGNodeName l) n s
                                               $ Result [] Nothing)
                 $ zip nodes sls
  listFinder <- setListData trvFinder fname []

  -- setup view selection actions
  setListSelectorSingle trvFinder $ do
                        selector <- treeViewGetSelection trvFinder
                        miter <- treeSelectionGetSelected selector
                        case miter of
                          Just _ -> widgetSetSensitive btnCheck True
                          Nothing -> widgetSetSensitive btnCheck False
  selection <- setListSelectorMultiple trvNodes btnNodesAll btnNodesNone
                 btnNodesInvert $ updateNodes trvNodes listNodes
                                    (updateFinder trvFinder listFinder)
                                    (do listStoreClear listFinder
                                        activate widgets False
                                        widgetSetSensitive btnCheck False)
                                    (do activate widgets True
                                        widgetSetSensitive btnCheck False)


  -- bindings
  onClicked btnNodesUnchecked $ do
    mModel <- treeViewGetModel trvNodes
    case mModel of
      Nothing -> return ()
      Just m -> do
        writeIORef selection []
        selector <- treeViewGetSelection trvNodes
        treeModelForeach m $ \ iter -> do
          path@(row:[]) <- treeModelGetPath m iter
          (FNode { model = Result d ms}) <- listStoreGetValue listNodes row
          if null d && isNothing ms then do
              treeSelectionSelectIter selector iter
              modifyIORef selection (path:)
            else treeSelectionUnselectIter selector iter
          return False
  onClicked btnNodesTimeout $ return ()

  onClicked btnModels $ forkIO_ $ showModelView mView "Models" listNodes
  onClicked btnClose $ widgetDestroy window
  onClicked btnFineGrained $ fineGrainedSelection trvFinder listFinder
                           $ widgetSetSensitive btnCheck True
  onClicked btnStop $ forkIO_ $ do
    mtid <- readMVar run
    maybe (return ()) killThread mtid
    takeMVar run
    return ()
  onClicked btnCheck $ forkIO_ $ do
    takeMVar run
    postGUISync $ activate checkWidgets False
    (update, exit) <- progressBar "Checking consistency" "please wait..."
    nodes' <- postGUISync $ getSelectedMultiple trvNodes listNodes
    mf <- postGUISync $ getSelectedSingle trvFinder listFinder
    f <- case mf of
      Nothing -> error "Consistency checker: internal error"
      Just (_,f) -> return f
    check ln le dg f update run listNodes nodes'
    postGUISync $ switch False
    putMVar run Nothing
    forkIO_ $ showModelView mView "Models" listNodes
    postGUISync $ switch True
    postGUISync $ activate checkWidgets True
    exit

  widgetShow window

-- | Get a markup string containing name and color
getFNodeName :: FNode -> String
getFNodeName (FNode { name = n, model = Result d m }) =
  let c = if null d && isNothing m then "black"
            else if hasErrors d then "red"  else "green"
  in "<span color=\"" ++ c ++ "\">" ++ n ++ "</span>"

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore FNode -> (G_sublogics -> IO ())
            -> IO () -> IO () -> IO ()
updateNodes view listNodes update lock unlock = do
  nodes <- getSelectedMultiple view listNodes
  if null nodes then lock
    else let sls = map (sublogic . snd) nodes in
      maybe lock (\ sl -> do unlock; update sl)
            $ foldl (\ ma b -> case ma of
                      Just a -> comSublogics b a
                      Nothing -> Nothing) (Just $ head sls) $ tail sls

-- | Update the list of finder
updateFinder :: TreeView -> ListStore Finder -> G_sublogics -> IO ()
updateFinder view list sl = forkIO_ $ do
  (update, exit) <- pulseBar "Calculating paths" "please wait..."
  postGUISync $ listStoreClear list
  mapM_ ( (postGUISync . listStoreAppend list)
        . (\ f -> f { selected = length (comorphs f) - 1}))
    $ Map.elems
    $ foldr (\ (cc,c) m -> let n = getPName cc
                               f = Map.findWithDefault (Finder n cc [] 0) n m in
              Map.insert n (f { comorphs = c : comorphs f}) m) Map.empty
    $ getConsCheckersAutomatic $ findComorphismPaths logicGraph sl
  update "finished"
  exit
  postGUIAsync $ selectFirst view

activate :: [Widget] -> Bool -> IO ()
activate widgets active = mapM_ (\ w -> widgetSetSensitive w active) widgets

check :: LIB_NAME -> LibEnv -> DGraph -> Finder -> (Double -> String -> IO ())
      -> MVar (Maybe ThreadId) -> ListStore FNode -> [(Int,FNode)] -> IO ()
check ln le dg (Finder { finder = cc, comorphs = cs, selected = i})
      update run list nodes = do
  tid <- forkIO $ do
    let count' = fromIntegral $ length nodes
        c = cs !! i
    foldM_ (\ count (row, fn@(FNode { node = n@(_,l), model = m })) -> do
             let name' = getDGNodeName l
             update (count / count') name'
             res <- consistencyCheck cc c ln le dg n
             postGUIAsync $ listStoreSetValue list row
                          $ fn { model = joinResult m res }
             return $ count+1) 0 nodes
    takeMVar run
    return ()
  putMVar run $ Just tid

fineGrainedSelection :: TreeView -> ListStore Finder -> IO () -> IO ()
fineGrainedSelection view list unlock = forkIO_ $ do
  paths <- postGUISync $ listStoreToList list
  selector <- treeViewGetSelection view
  if null paths then error "Cant make selection without sublogic!"
    else do
      ret <- listChoiceAux "Choose a translation"
               (\ (n,_,c) -> n ++ ": " ++ show c) $ concatMap expand paths
      case ret of
        Just (_,(n,_,c)) -> case findIndex ((n ==) . fname) paths of
          Just i -> let f = paths !! i in case findIndex (c ==) $ comorphs f of
            Just i' -> postGUISync $ do
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
showModelViewAux lock title list = postGUISync $ do
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
  nodes <- listStoreToList list
  listNodes <- setListData trvNodes name
    -- TODO: filter hasErrors d
    $ filter ((\ (Result d m) -> not (null d && isNothing m)) . model) nodes

  setListSelectorSingle trvNodes $ do
    mn <- getSelectedSingle trvNodes listNodes
    case mn of
      Nothing -> textBufferSetText buffer ""
      Just (_,n) -> textBufferSetText buffer $ unlines $ map diagString $ diags
                                             $ model n

  -- setup actions
  onClicked btnClose $ widgetDestroy window
  onDestroy window $ do takeMVar lock; return ()

  putMVar lock $ return ()

  widgetSetSizeRequest window 800 600
  widgetSetSizeRequest frNodes 250 (-1)

  widgetShow window

-- | Displays the model view window
showModelView :: MVar (IO ()) -> String -> ListStore FNode -> IO ()
showModelView lock title list  = do
  isNotOpen <- isEmptyMVar lock
  if isNotOpen then showModelViewAux lock title list
    else join (readMVar lock)

