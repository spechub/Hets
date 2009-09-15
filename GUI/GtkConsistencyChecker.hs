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
import Control.Monad (foldM_)

import Proofs.AbstractState
import Proofs.InferBasic (consistencyCheck)

import Data.IORef
import Data.Graph.Inductive.Graph (LNode)
import qualified Data.Map as Map
import Data.List (findIndex)

data Finder = Finder { fname :: String
                     , finder :: G_cons_checker
                     , comorphs :: [AnyComorphism]
                     , selected :: Int }

data FNode = FNode { name :: String
                   , node :: LNode DGNodeLab
                   --, theory :: G_theory
                   , sublogic :: G_sublogics }

-- | Displays the consistency checker window
showConsistencyChecker :: GInfo -> IO ()
showConsistencyChecker gInfo@(GInfo { libName = ln }) = postGUIAsync $ do
  xml            <- getGladeXML ConsistencyChecker.get
  -- get objects
  window         <- xmlGetWidget xml castToWindow "ConsistencyChecker"
  btnClose       <- xmlGetWidget xml castToButton "btnClose"
  -- get nodes view and buttons
  trvNodes       <- xmlGetWidget xml castToTreeView "trvNodes"
  btnNodesAll    <- xmlGetWidget xml castToButton "btnNodesAll"
  btnNodesNone   <- xmlGetWidget xml castToButton "btnNodesNone"
  btnNodesInvert <- xmlGetWidget xml castToButton "btnNodesInvert"
  -- get checker view and buttons
  lblStatus      <- xmlGetWidget xml castToLabel "lblStatus"
  lblSublogic    <- xmlGetWidget xml castToLabel "lblSublogic"
  sbTimeout      <- xmlGetWidget xml castToSpinButton "sbTimeout"
  btnCheck       <- xmlGetWidget xml castToButton "btnCheck"
  btnStop        <- xmlGetWidget xml castToButton "btnStop"
  btnFineGrained <- xmlGetWidget xml castToButton "btnFineGrained"
  trvFinder      <- xmlGetWidget xml castToTreeView "trvFinder"

  windowSetTitle window "Consistency Checker"

  let widgets = [ toWidget trvFinder, toWidget btnFineGrained
                , toWidget sbTimeout, toWidget lblStatus, toWidget lblSublogic]
      checkWidgets = widgets ++ [ toWidget btnClose, toWidget trvNodes
                                , toWidget btnNodesAll, toWidget btnNodesNone
                                , toWidget btnNodesInvert]
  widgetSetSensitive btnStop False
  widgetSetSensitive btnCheck False

  run <- newMVar Nothing
  res <- newEmptyMVar

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
  listNodes <- setListData trvNodes name
                 $ map (\ (n@(_,l),s) -> FNode (getDGNodeName l) n s)
                 $ zip nodes sls
  listFinder <- setListData trvFinder fname []

  -- setup view selection actions
  setListSelectorSingle trvFinder $ do
                        selector <- treeViewGetSelection trvFinder
                        miter <- treeSelectionGetSelected selector
                        case miter of
                          Just _ -> widgetSetSensitive btnCheck True
                          Nothing -> widgetSetSensitive btnCheck False
  setListSelectorMultiple trvNodes btnNodesAll btnNodesNone btnNodesInvert
                          $ updateNodes trvNodes listNodes listFinder
                          (do listStoreClear listFinder
                              activate widgets False
                              widgetSetSensitive btnCheck False)
                          (do activate widgets True
                              widgetSetSensitive btnCheck False)

  -- bindings
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
    nodes' <- postGUISync $ getNodes trvNodes listNodes
    f <- postGUISync $ getFinder trvFinder listFinder
    check ln le dg f update run (map node nodes') res
    postGUISync $ switch False
    putMVar run Nothing
    res' <- takeMVar res
    let mes = unlines $ concatMap (\ (n,r) -> ("\nModel for: " ++ n ++ "\n") :
                                              map diagString (diags r)) res'
    textView "Result of consistency check" mes Nothing
    postGUISync $ switch True
    postGUISync $ activate checkWidgets True
    exit

  widgetShow window

-- | Get selected finder
getNodes :: TreeView -> ListStore FNode -> IO [FNode]
getNodes view list = do
  selector <- treeViewGetSelection view
  rows <- treeSelectionGetSelectedRows selector
  mapM (listStoreGetValue list . head) rows

-- | Get selected nodes
getFinder :: TreeView -> ListStore Finder -> IO Finder
getFinder view list = do
  selector <- treeViewGetSelection view
  (Just model) <- treeViewGetModel view
  (Just iter) <- treeSelectionGetSelected selector
  (row:[]) <- treeModelGetPath model iter
  listStoreGetValue list row

-- | Called when node selection is changed. Updates finder list
updateNodes :: TreeView -> ListStore FNode -> ListStore Finder
            -> IO () -> IO () -> IO ()
updateNodes view listNodes listFinder lock unlock = do
  nodes <- getNodes view listNodes
  if null nodes then lock
    else let sls = map sublogic nodes in
      maybe lock (\ sl -> do unlock; updateFinder listFinder sl)
            $ foldl (\ ma b -> case ma of
                      Just a -> comSublogics b a
                      Nothing -> Nothing) (Just $ head sls) $ tail sls

-- | Update the list of finder
updateFinder :: ListStore Finder -> G_sublogics -> IO ()
updateFinder list sl = forkIO_ $ do
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

activate :: [Widget] -> Bool -> IO ()
activate widgets active = mapM_ (\ w -> widgetSetSensitive w active) widgets

check :: LIB_NAME -> LibEnv -> DGraph -> Finder -> (Double -> String -> IO ())
      -> MVar (Maybe ThreadId) -> [LNode DGNodeLab]
      -> MVar [(String, Result G_theory)] -> IO ()
check ln le dg (Finder { finder = cc, comorphs = cs, selected = i})
      update run nodes res = do
  putMVar res []
  tid <- forkIO $ do
    let count' = fromIntegral $ length nodes
        c = cs !! i
    foldM_ (\ count n@(_,l) -> do
             let name' = getDGNodeName l
             update (count / count') name'
             res' <- consistencyCheck cc c ln le dg n
             modifyMVar_ res (return . ((name',res'):))
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
        Just (n,_,c) -> case findIndex ((n ==) . fname) paths of
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
