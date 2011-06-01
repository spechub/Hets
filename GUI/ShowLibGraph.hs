{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  unstable
Portability :  non-portable

This Modul provides a function to display a Library Dependency Graph.
-}

module GUI.ShowLibGraph
  ( showLibGraph
  , mShowGraph
  , closeOpenWindows
  ) where

import Driver.Options (HetcatsOpts (outtypes, verbose), putIfVerbose)
import Driver.WriteFn (writeVerbFile)
import Driver.ReadFn
import Driver.AnaLib

import Static.DevGraph
import Static.History
import Static.ToXml as ToXml
import Static.ApplyChanges

import GUI.UDGUtils as UDG
import GUI.Utils

import GUI.GraphTypes
import GUI.GraphLogic (translateGraph, showDGraph)
import GUI.ShowLogicGraph (showLogicGraph)
import GUI.GraphDisplay
import qualified GUI.GraphAbstraction as GA

import Common.LibName
import Common.Utils
import qualified Common.Lib.Rel as Rel
import Common.Result

import Data.IORef
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

import Control.Concurrent.MVar
import Control.Monad

import Interfaces.DataTypes
import Interfaces.Utils

import Text.XML.Light (ppTopElement)

import System.Process

type NodeEdgeList = ([DaVinciNode LibName], [DaVinciArc (IO String)])

{- | Creates a  new uDrawGraph Window and shows the Library Dependency Graph of
     the given LibEnv. -}
showLibGraph :: LibFunc
showLibGraph gi = do
  let lock = libGraphLock gi
  isEmpty <- isEmptyMVar lock
  when isEmpty $ do
    putMVar lock ()
    updateWindowCount gi succ
    graph <- newIORef daVinciSort
    nodesEdges <- newIORef (([], []) :: NodeEdgeList)
    let
      globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [ Button "Reload Library" $ reloadLibGraph gi graph nodesEdges
          , Button "Experimental reload changed Library"
                       $ changeLibGraph gi graph nodesEdges
          , Button "Translate Library" $ translate gi
          , Button "Show Logic Graph" $ showLogicGraph daVinciSort
          ])
      graphParms = globalMenu $$
                   GraphTitle "Library Graph" $$
                   OptimiseLayout True $$
                   AllowClose (closeGInfo gi) $$
                   FileMenuAct ExitMenuOption (Just (exitGInfo gi)) $$
                   emptyGraphParms
    graph' <- newGraph daVinciSort graphParms
    addNodesAndEdges gi graph' nodesEdges
    writeIORef graph graph'
    redraw graph'

closeGInfo :: GInfo -> IO Bool
closeGInfo gi = do
  updateWindowCount gi pred
  takeMVar (libGraphLock gi)
  return True

-- | Reloads all Libraries and the Library Dependency Graph
reloadLibGraph :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeEdgeList
               -> IO ()
reloadLibGraph gi graph nodesEdges = do
  b <- warningDialog "Reload library" warnTxt
  when b $ reloadLibGraph' gi graph nodesEdges

warnTxt :: String
warnTxt = unlines
  [ "Are you sure to recreate Library?"
  , "All development graph windows will be closed and proofs will be lost."
  , "", "This operation can not be undone." ]

-- | Reloads all Libraries and the Library Dependency Graph
reloadLibGraph' :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeEdgeList
                -> IO ()
reloadLibGraph' gi graph nodesEdges = do
  graph' <- readIORef graph
  (nodes, edges) <- readIORef nodesEdges
  let ln = libName gi
      libfile = libNameToFile ln
  m <- anaLib (hetcatsOpts gi) { outtypes = [] } libfile
  case m of
    Nothing -> errorDialog "Error" $ "Error when reloading file '"
                                     ++ libfile ++ "'"
    Just (_, le) -> do
      closeOpenWindows gi
      mapM_ (deleteArc graph') edges
      mapM_ (deleteNode graph') nodes
      addNodesAndEdges gi graph' nodesEdges
      writeIORef graph graph'
      redraw graph'
      writeIORef (intState gi) emptyIntState
                 { i_state = Just $ emptyIntIState le ln
                 , filename = libfile }
      mShowGraph gi ln

changeLibGraph :: GInfo -> IORef DaVinciGraphTypeSyn -> IORef NodeEdgeList
  -> IO ()
changeLibGraph gi graph nodesEdges = do
  let ln = libName gi
      opts = hetcatsOpts gi
  ost <- readIORef $ intState gi
  graph' <- readIORef graph
  (nodes, edges) <- readIORef nodesEdges
  gmocPath <- getEnvDef "HETS_GMOC" ""
  case i_state ost of
    Nothing -> return ()
    Just ist -> if null gmocPath then
      errorDialog "Error" "HETS_GMOC variable not set" else do
      let le = i_libEnv ist
          dg = lookupDGraph ln le
          fn = libNameToFile ln
          f1 = fn ++ ".xhi"
          f2 = fn ++ ".old.xh"
          f3 = fn ++ ".new.xh"
          dgold = changesDGH dg $ map negateChange $ flatHistory
                  $ proofHistory dg
          writeXml l' f' g' =
              writeVerbFile opts f' $ ppTopElement
                $ ToXml.dGraph l' ln g'
      writeXml le f1 dg
      writeXml le f2 dgold
      m <- anaLib opts { outtypes = [] } fn
      case m of
        Just (nln, nle) | nln == ln -> do
          let dg2 = lookupDGraph nln nle
              ndg = changesDGH dg2 $ map negateChange $ flatHistory
                  $ proofHistory dg2
          writeXml nle f3 ndg
          md <- withinDirectory gmocPath $ do
            (_, exitPulse) <- pulseBar "Gmoc" "calling bin/gmoc ..."
            output <- readProcess "bin/gmoc"
              ["-c", "Configuration.xml", "-itype", "file", "moc", f2, f1, f3]
              ""
            exitPulse
            let getFile pre =
                  listToMaybe $ mapMaybe (stripPrefix pre) $ lines output
            return $ liftM2 (,) (getFile "xupdates: ") $ getFile "Impacts: "
          case md of
            Nothing -> errorDialog "Error" "no xupdate file found"
            Just (xd, xi) -> do
              putIfVerbose opts 2 $ "Reading " ++ xd
              xs <- readFile xd
              xis <- readFile xi
              putIfVerbose opts 3 $ "Ignoring Impacts:\n" ++ xis
              let Result ds mdg = dgXUpdate xs le dg
              case mdg of
                Just fdg -> do
                  closeOpenWindows gi
                  mapM_ (deleteArc graph') edges
                  mapM_ (deleteNode graph') nodes
                  addNodesAndEdges gi graph' nodesEdges
                  writeIORef graph graph'
                  redraw graph'
                  let fle = Map.insert ln fdg le
                  writeIORef (intState gi) emptyIntState
                        { i_state = Just $ emptyIntIState fle ln
                        , filename = fn }
                  mShowGraph gi ln
                Nothing ->
                  errorDialog "Error" $ showRelDiags (verbose opts) ds
        _ -> errorDialog "Error" $ "Error when reloading file '" ++ fn ++ "'"

-- | Translate Graph
translate :: GInfo -> IO ()
translate gi = do
  b <- warningDialog "Translate library" warnTxt
  when b $ translate' gi

-- | Translate Graph
translate' :: GInfo -> IO ()
translate' gi = do
  mle <- translateGraph gi
  case mle of
    Just le -> do
      closeOpenWindows gi
      let ln = libName gi
          ost = emptyIntState
          nwst = case i_state ost of
            Nothing -> ost
            Just ist -> ost { i_state = Just $ ist { i_libEnv = le
                                                   , i_ln = ln }
                            , filename = libNameToFile ln }
      writeIORef (intState gi) nwst
      mShowGraph gi ln
    Nothing -> return ()

-- | closes the open graphs to be reopened later
closeOpenWindows :: GInfo -> IO ()
closeOpenWindows gi = do
  let iorOpenGraphs = openGraphs gi
  oGraphs <- readIORef iorOpenGraphs
  mapM_ (GA.closeGraphWindow . graphInfo) $ Map.elems oGraphs
  updateWindowCount gi (const 1)
  writeIORef iorOpenGraphs Map.empty

-- | Adds the Librarys and the Dependencies to the Graph
addNodesAndEdges :: GInfo -> DaVinciGraphTypeSyn -> IORef NodeEdgeList -> IO ()
addNodesAndEdges gi graph nodesEdges = do
 ost <- readIORef $ intState gi
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    opts = hetcatsOpts gi
    lookup' x y = Map.findWithDefault
      (error $ "lookup2': node not found " ++ show y) y x
    keySet = Map.keysSet le
    keys = Set.toList keySet
    subNodeMenu = LocalMenu (UDG.Menu Nothing [
      Button "Show Graph" $ mShowGraph gi,
      Button "Show spec/View Names" $ showSpec le])
    subNodeTypeParms = subNodeMenu $$$
                       Box $$$
                       ValueTitle (return . show) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   subNodeList <- mapM (newNode graph subNodeType) keys
   let
    nodes' = Map.fromList $ zip keys subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle id $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (node1, node2) = newArc graph subArcType (return "")
                                            (lookup' nodes' node1)
                                            (lookup' nodes' node2)
   subArcList <- mapM insertSubArc $ getLibDeps keySet le
   writeIORef nodesEdges (subNodeList, subArcList)

-- | Creates a list of all LibName pairs, which have a dependency
getLibDeps :: Set.Set LibName -> LibEnv -> [(LibName, LibName)]
getLibDeps ks =
  Rel.toList . Rel.intransKernel . (`Rel.restrict` ks) . getLibDepRel

mShowGraph :: GInfo -> LibName -> IO ()
mShowGraph gi ln = showDGraph gi ln convertGraph showLibGraph

-- | Displays the Specs of a Library in a Textwindow
showSpec :: LibEnv -> LibName -> IO ()
showSpec le ln =
  createTextDisplay ("Contents of " ++ show ln)
                    $ unlines . map show . Map.keys . globalEnv
                    $ lookupDGraph ln le
