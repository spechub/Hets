{- |
Module      :  $Header$
Description :  Logic for manipulating the graph in the  Central GUI
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

This module provides functions for all the menus in the Hets GUI.
These are then assembled to the GUI in "GUI.GraphMenu".

-}

module GUI.GraphLogic
    ( undo
    , reload
    , performProofAction
    , openProofStatus
    , saveProofStatus
    , nodeErr
    , proofMenu
    , openTranslateGraph
    , showReferencedLibrary
    , showSpec
    , getTheoryOfNode
    , translateTheoryOfNode
    , displaySubsortGraph
    , displayConceptGraph
    , lookupTheoryOfNode
    , showProofStatusOfNode
    , proveAtNode
    , showNodeInfo
    , showEdgeInfo
    , checkconservativityOfEdge
    , convert
    , hideNodes
    , getLibDeps
    , hideShowNames
    , showNodes
    , translateGraph
    , showLibGraph
    , runAndLock
    , saveUDGraph
    , focusNode
    , applyChanges
    ) where

import Logic.Logic(conservativityCheck)
import Logic.Coerce(coerceSign, coerceMorphism)
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover
import CASL.CCC.FreeTypes
import Comorphisms.LogicGraph(logicGraph)

import Syntax.AS_Library(LIB_NAME, getModTime, getLIB_ID)

import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.DGToSpec(dgToSpec)
import Static.AnalysisLibrary(anaLibExt, anaLib)
import Static.DGTranslation(libEnv_translation)

import Proofs.EdgeUtils
import Proofs.InferBasic(basicInferenceNode)
import Proofs.StatusUtils(lookupHistory, removeContraryChanges)
import Proofs.TheoremHideShift

import GUI.Utils (listBox, createTextSaveDisplay)
import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)
import GUI.DGTranslation(getDGLogic)
import GUI.GraphTypes
import qualified GUI.GraphAbstraction as GA
import qualified GUI.HTkUtils (displayTheoryWithWarning,
                               createInfoDisplayWithTwoButtons)

import GraphConfigure
import TextDisplay(createTextDisplay)
import InfoBus(encapsulateWaitTermAct)
import DialogWin (useHTk)
import Messages(errorMess)
import qualified HTk
import Configuration(size)
import FileDialog(newFileDialogStr)

import Common.DocUtils (showDoc)
import Common.ResultT(liftR, runResultT)
import Common.AS_Annotation(isAxiom)
import Common.Result as Res
import Common.ExtSign
import qualified Common.OrderedMap as OMap
import qualified Common.Lib.Rel as Rel

import Driver.Options
import Driver.WriteFn(writeShATermFile)
import Driver.ReadFn(libNameToFile, readVerbose)

import System.Directory(getModificationTime)

import Data.IORef
import Data.Char(toLower)
import Data.Maybe(fromJust)
import Data.List(partition)
import Data.Graph.Inductive.Graph (Node, LEdge, LNode)
import qualified Data.Map as Map

import Control.Monad(foldM, filterM)
import Control.Monad.Trans(lift)
import Control.Concurrent.MVar

-- | Locks the global lock and runs function
runAndLock :: GInfo -> IO () -> IO ()
runAndLock (GInfo { functionLock = lock
                  , gi_GraphInfo = actGraphInfo
                  }) function = do
  locked <- tryPutMVar lock ()
  case locked of
    True -> do
      GA.deactivateGraphWindow actGraphInfo
      function
      takeMVar lock
      GA.redisplay actGraphInfo
      GA.layoutImproveAll actGraphInfo
      GA.activateGraphWindow actGraphInfo
    False ->
      GA.showTemporaryMessage actGraphInfo
        $ "an other function is still working ... please wait ..."

-- | negate change
negateChange :: DGChange -> DGChange
negateChange change = case change of
      InsertNode x -> DeleteNode x
      DeleteNode x -> InsertNode x
      InsertEdge x -> DeleteEdge x
      DeleteEdge x -> InsertEdge x
      SetNodeLab old (node, new) -> SetNodeLab new (node, old)

-- | Undo one step of the History
undo :: GInfo -> Bool -> IO ()
undo gInfo@(GInfo { globalHist = gHist
                  , gi_GraphInfo = actGraph
                  }) isUndo = do
  (guHist, grHist) <- takeMVar gHist
  case if isUndo then guHist else grHist of
    [] -> do
       GA.showTemporaryMessage actGraph "History is empty..."
       putMVar gHist (guHist, grHist)
    (lns:gHist') -> do
      undoDGraphs gInfo isUndo lns
      putMVar gHist $ if isUndo then (gHist', reverse lns : grHist)
                                else (reverse lns : guHist, gHist')

undoDGraphs :: GInfo -> Bool -> [LIB_NAME] -> IO ()
undoDGraphs _ _ []     = return ()
undoDGraphs g u (ln:r) = do
  undoDGraph g u ln
  undoDGraphs g u r

undoDGraph :: GInfo -> Bool -> LIB_NAME -> IO ()
undoDGraph gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                        , gi_GraphInfo = actGraph
                        }) isUndo ln = do
  GA.showTemporaryMessage actGraph $
        (if isUndo then "Un" else "Re") ++ "do last change to "
        ++ show ln ++ "..."
  lockGlobal gInfo
  le <- readIORef ioRefProofStatus
  let
    dg = lookupDGraph ln le
    hist = (proofHistory dg, redoHistory dg)
    swap (a, b) = (b, a)
    (phist, rhist) = (if isUndo then id else swap) hist
    (cl@(rs, cs), newHist) = case phist of
           hd : tl -> (hd, (tl, hd : rhist))
           _ -> error "undoDGraph"
    (newPHist, newRHist) = (if isUndo then id else swap) newHist
    change = if isUndo then (reverse rs, reverse $ map negateChange cs)
             else cl
    dg' = (changesDG dg $ snd change)
          { proofHistory = newPHist
          , redoHistory = newRHist }
  writeIORef ioRefProofStatus $ Map.insert ln dg' le
  case openlock dg' of
    Nothing -> return ()
    Just lock -> do
      mvar <- tryTakeMVar lock
      case mvar of
        Nothing -> return ()
        Just applyHist -> do
          applyHist [change]
          putMVar lock applyHist
  unlockGlobal gInfo

-- | reloads the Library of the DevGraph
reload :: GInfo -> IO()
reload gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                    , gi_LIB_NAME = ln
                    , gi_hetcatsOpts = opts
                    , gi_GraphInfo = actGraphInfo
                    }) = do
  lockGlobal gInfo
  oldle <- readIORef ioRefProofStatus
  let
    libdeps = Rel.toList $ Rel.intransKernel $ Rel.transClosure $ Rel.fromList
              $ getLibDeps oldle
  ioruplibs <- newIORef ([] :: [LIB_NAME])
  writeIORef ioruplibs []
  reloadLibs ioRefProofStatus opts libdeps ioruplibs ln
  unlockGlobal gInfo
  libs <- readIORef ioruplibs
  case libs of
    [] -> GA.showTemporaryMessage actGraphInfo "Reload not needed!"
    _ -> remakeGraph gInfo

-- | Creates a list of all LIB_NAME pairs, which have a dependency
getLibDeps :: LibEnv -> [(LIB_NAME, LIB_NAME)]
getLibDeps le =
  concat $ map (\ ln -> getDep ln le) $ Map.keys le

-- | Creates a list of LIB_NAME pairs for the fist argument
getDep :: LIB_NAME -> LibEnv -> [(LIB_NAME, LIB_NAME)]
getDep ln le = map (\ (_, x) -> (ln, dgn_libname x)) $
  filter (isDGRef . snd) $ labNodesDG $ lookupDGraph ln le

-- | Reloads a library
reloadLib :: IORef LibEnv -> HetcatsOpts -> IORef [LIB_NAME] -> LIB_NAME
          -> IO ()
reloadLib iorle opts ioruplibs ln = do
  mfile <- existsAnSource opts {intype = GuessIn}
           $ rmSuffix $ libNameToFile opts ln
  case mfile of
    Nothing -> return ()
    Just file -> do
      le <- readIORef iorle
      mFunc <- case openlock $ lookupDGraph ln le of
        Just lock -> tryTakeMVar lock
        Nothing -> return Nothing
      let
        le' = Map.delete ln le
      mres <- anaLibExt opts file le'
      case mres of
        Just (_, newle) -> do
          uplibs <- readIORef ioruplibs
          writeIORef ioruplibs $ ln:uplibs
          case mFunc of
            Just func -> case openlock $ lookupDGraph ln newle of
              Just lock -> putMVar lock func
              Nothing -> errorMess "Reload: Can't set openlock in DevGraph"
            Nothing -> return ()
          writeIORef iorle $ newle
        Nothing ->
          errorMess $ "Could not read original development graph from "
            ++ show file

-- | Reloads libraries if nessesary
reloadLibs :: IORef LibEnv -> HetcatsOpts -> [(LIB_NAME, LIB_NAME)]
           -> IORef [LIB_NAME] -> LIB_NAME -> IO Bool
reloadLibs iorle opts deps ioruplibs ln = do
  uplibs <- readIORef ioruplibs
  case elem ln uplibs of
    True -> return True
    False -> do
      let
        deps' = map (snd) $ filter (\ (ln',_) -> ln == ln') deps
      res <- mapM (reloadLibs iorle opts deps ioruplibs) deps'
      let
        libupdate = foldl (\ u r -> if r then True else u) False res
      case libupdate of
        True -> do
          reloadLib iorle opts ioruplibs ln
          return True
        False -> do
          le <- readIORef iorle
          let
            newln:_ = filter (ln ==) $ Map.keys le
          mfile <- existsAnSource opts $ rmSuffix $ libNameToFile opts ln
          case mfile of
            Nothing -> return False
            Just file -> do
              newmt <- getModificationTime file
              let
                libupdate' = (getModTime $ getLIB_ID newln) < newmt
              case libupdate' of
                False -> return False
                True -> do
                  reloadLib iorle opts ioruplibs ln
                  return True

-- | Deletes the old edges and nodes of the Graph and makes new ones
remakeGraph :: GInfo -> IO ()
remakeGraph gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                         , gi_LIB_NAME = ln
                         , gi_GraphInfo = actGraphInfo
                         }) = do
  le <- readIORef ioRefProofStatus
  let
    dgraph = lookupDGraph ln le
  showNodes gInfo
  GA.clear actGraphInfo
  convert actGraphInfo dgraph
  hideNodes gInfo

-- | Toggles to display internal node names
hideShowNames :: GInfo -> Bool -> IO ()
hideShowNames (GInfo { internalNamesIORef = showInternalNames
                     }) toggle = do
  (intrn::InternalNames) <- readIORef showInternalNames
  let showThem = if toggle then not $ showNames intrn else showNames intrn
      showItrn s = if showThem then s else ""
  mapM_ (\(s,upd) -> upd (\_ -> showItrn s)) $ updater intrn
  writeIORef showInternalNames $ intrn {showNames = showThem}

-- | shows all hidden nodes and edges
showNodes :: GInfo -> IO ()
showNodes gInfo@(GInfo { gi_GraphInfo = actGraphInfo
                       }) = do
  hhn <- GA.hasHiddenNodes actGraphInfo
  case hhn of
    True -> do
      GA.showTemporaryMessage actGraphInfo "Revealing hidden nodes ..."
      GA.showAll actGraphInfo
      hideShowNames gInfo False
    False -> do
      GA.showTemporaryMessage actGraphInfo "No hidden nodes found ..."

-- | hides all unnamed internal nodes that are proven
hideNodes :: GInfo -> IO ()
hideNodes (GInfo { libEnvIORef = ioRefProofStatus
                 , gi_LIB_NAME = ln
                 , gi_GraphInfo = actGraphInfo
                 }) = do
  hhn <- GA.hasHiddenNodes actGraphInfo
  case hhn of
    True ->
      GA.showTemporaryMessage actGraphInfo "Nodes already hidden ..."
    False -> do
      GA.showTemporaryMessage actGraphInfo "Hiding unnamed nodes..."
      le <- readIORef ioRefProofStatus
      let dg = lookupDGraph ln le
          nodes = selectNodesByType dg [LocallyEmptyProvenConsInternal]
          edges = getCompressedEdges dg nodes
      GA.hideNodes actGraphInfo nodes edges

-- | selects all nodes of a type with outgoing edges
selectNodesByType :: DGraph -> [DGNodeType] -> [Node]
selectNodesByType dg types =
  filter (\ n -> outDG dg n /= []) $ map fst
         $ filter (\ (_, n) -> elem (getRealDGNodeType n) types) $ labNodesDG dg

-- | compresses a list of types to the highest one
compressTypes :: [DGEdgeType] -> DGEdgeType
compressTypes [] = error "compressTypes: wrong usage"
compressTypes (t:[]) = t
compressTypes (t1:t2:r) = case t1 > t2 of
  True -> compressTypes (t1:r)
  False -> compressTypes (t2:r)

-- | returns a list of compressed edges
getCompressedEdges :: DGraph -> [Node] -> [(Node,Node,DGEdgeType)]
getCompressedEdges dg hidden =
  filterDuplicates $ getShortPaths $ concat
                   $ map (\ e@(_,t,_) -> map (e:) $ getPaths dg t hidden [])
                         inEdges
  where
    inEdges = filter (\ (_,t,_) -> elem t hidden)
                     $ concat $ map (outDG dg)
                     $ foldr (\ n i -> if elem n hidden
                                       || elem n i then i else n:i) []
                     $ map (\ (s,_,_) -> s) $ concat $ map (innDG dg) hidden

-- | filter duplicate paths
filterDuplicates :: [(Node,Node,DGEdgeType)]
                 -> [(Node,Node,DGEdgeType)]
filterDuplicates [] = []
filterDuplicates ((s,t,et):r) = edge:filterDuplicates others
  where
    (same,others) = partition (\ (s',t',_) -> s == s' && t == t') r
    edge = (s,t,compressTypes $ et:map (\ (_,_,et') -> et') same)

-- | returns the pahts of a given node through hidden nodes
getPaths :: DGraph -> Node -> [Node] -> [Node] -> [[LEdge DGLinkLab]]
getPaths dg node hidden seen' = case elem node hidden of
  True -> case edges /= [] of
    True -> concat $ map (\ e@(_,t,_) -> map (e:) $ getPaths dg t hidden seen)
                         edges
    False -> []
  False -> [[]]
  where
    seen = node:seen'
    edges = filter (\ (_,t,_) -> notElem t seen) $ outDG dg node

-- | returns source and target node of a path with the compressed type
getShortPaths :: [[LEdge DGLinkLab]]
              -> [(Node,Node,DGEdgeType)]
getShortPaths [] = []
getShortPaths (p:r) =
  ((s,t,compressTypes $ map (\ (_,_,e) -> getRealDGLinkType e) p))
    : getShortPaths r
  where
    (s,_,_) = head p
    (_,t,_) = last p

-- | Let the user select a Node to focus
focusNode :: GInfo -> IO ()
focusNode (GInfo { libEnvIORef = ioRefProofStatus
                 , gi_LIB_NAME = ln
                 ,gi_GraphInfo = grInfo
                 }) = do
  le <- readIORef ioRefProofStatus
  idsnodes <- filterM (\(n,_) -> do b <- GA.isHiddenNode grInfo n
                                    return $ not b)
                    $ labNodesDG $ lookupDGraph ln le
  let (ids,nodes) = unzip idsnodes
  let nodes' = map (getDGNodeName) nodes
  selection <- listBox "Select a node to focus" nodes'
  case selection of
    Just idx -> GA.focusNode grInfo $ ids !! idx
    Nothing -> return ()

translateGraph :: GInfo -> ConvFunc -> LibFunc -> IO ()
translateGraph (GInfo {libEnvIORef = ioRefProofStatus,
                       gi_LIB_NAME = ln,
                       gi_hetcatsOpts = opts
                      }) convGraph showLib = do
  le <- readIORef ioRefProofStatus
  openTranslateGraph le ln opts (getDGLogic le) convGraph showLib

showLibGraph :: GInfo -> LibFunc -> IO ()
showLibGraph gInfo showLib = do
  showLib gInfo
  return ()

{- | it tries to perform the given action to the given graph.
     If part of the given graph is not hidden, then the action can
     be performed directly; otherwise the graph will be shown completely
     firstly, and then the action will be performed, and after that the graph
     will be hidden again.
-}
performProofAction :: GInfo -> IO () -> IO ()
performProofAction gInfo@(GInfo { gi_GraphInfo = actGraphInfo
                                }) proofAction = do
  let actionWithMessage = do
          GA.showTemporaryMessage actGraphInfo
               "Applying development graph calculus proof rule..."
          proofAction
  hhn  <- GA.hasHiddenNodes actGraphInfo
  case hhn of
    True -> do
      showNodes gInfo
      actionWithMessage
      hideNodes gInfo
    False -> actionWithMessage
  GA.showTemporaryMessage actGraphInfo
                       "Development graph calculus proof rule finished."

saveProofStatus :: GInfo -> FilePath -> IO ()
saveProofStatus (GInfo { libEnvIORef = ioRefProofStatus
                       , gi_LIB_NAME = ln
                       , gi_hetcatsOpts = opts
                       }) file = encapsulateWaitTermAct $ do
    proofStatus <- readIORef ioRefProofStatus
    writeShATermFile file (ln, lookupHistory ln proofStatus)
    putIfVerbose opts 2 $ "Wrote " ++ file

-- | implementation of open menu, read in a proof status
openProofStatus :: GInfo -> FilePath -> ConvFunc -> LibFunc
                -> IO ()
openProofStatus gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                             , gi_LIB_NAME = ln
                             , gi_hetcatsOpts = opts
                             }) file convGraph showLib = do
    mh <- readVerbose opts ln file
    case mh of
      Nothing -> errorMess $ "Could not read proof status from file '"
                             ++ file ++ "'"
      Just h -> do
          let libfile = libNameToFile opts ln
          m <- anaLib opts { outtypes = [] } libfile
          case m of
            Nothing -> errorMess $ "Could not read original development graph"
                                   ++ " from '" ++ libfile ++  "'"
            Just (_, libEnv) -> case Map.lookup ln libEnv of
                Nothing -> errorMess $ "Could not get original development"
                                       ++ " graph for '" ++ showDoc ln "'"
                Just dg -> do
                    lockGlobal gInfo
                    oldEnv <- readIORef ioRefProofStatus
                    let proofStatus = Map.insert ln
                                      (applyProofHistory h dg) oldEnv
                    writeIORef ioRefProofStatus proofStatus
                    unlockGlobal gInfo
                    gInfo' <- copyGInfo gInfo ln
                    convGraph gInfo' "Proof Status " showLib
                    let actGraphInfo = gi_GraphInfo gInfo
                    GA.deactivateGraphWindow actGraphInfo
                    GA.redisplay actGraphInfo
                    GA.layoutImproveAll actGraphInfo
                    GA.activateGraphWindow actGraphInfo

-- | apply a rule of the development graph calculus
proofMenu :: GInfo
             -> (LibEnv -> IO (Res.Result LibEnv))
             -> IO ()
proofMenu gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                       , gi_LIB_NAME = ln
                       , gi_GraphInfo = actGraphInfo
                       , gi_hetcatsOpts = hOpts
                       , proofGUIMVar = guiMVar
                       , globalHist = gHist
                       }) proofFun = do
  filled <- tryPutMVar guiMVar Nothing
  if not filled
    then readMVar guiMVar >>=
                  (maybe (putIfVerbose hOpts 0 "proofMenu: ignored Nothing")
                         (\ w -> do
                             putIfVerbose hOpts 4 $
                                  "proofMenu: Ignored Proof command; " ++
                                  "maybe a proof window is still open?"
                             HTk.putWinOnTop w))
    else do
      lockGlobal gInfo
      proofStatus <- readIORef ioRefProofStatus
      putIfVerbose hOpts 4 "Proof started via \"Proofs\" menu"
      Res.Result ds res <- proofFun proofStatus
      putIfVerbose hOpts 4 "Analyzing result of proof"
      case res of
        Nothing -> do
          unlockGlobal gInfo
          printDiags 2 ds
        Just newProofStatus -> do
          let newGr = lookupDGraph ln newProofStatus
              history = proofHistory newGr
          (guHist, grHist) <- takeMVar gHist
          doDump hOpts "PrintHistory" $ do
            putStrLn "History"
            print $ prettyHistory history
          putMVar gHist
           (calcGlobalHistory proofStatus newProofStatus : guHist, grHist)
          applyChanges actGraphInfo history
          writeIORef ioRefProofStatus newProofStatus
          unlockGlobal gInfo
          hideShowNames gInfo False
          mGUIMVar <- tryTakeMVar guiMVar
          maybe (fail $ "should be filled with Nothing after proof attempt")
                (const $ return ())
                mGUIMVar

calcGlobalHistory :: LibEnv -> LibEnv -> [LIB_NAME]
calcGlobalHistory old new = let
    pHist = (\ ln le -> proofHistory $ lookupDGraph ln le)
    length' = (\ ln le -> length $ pHist ln le)
    changes = filter (\ ln -> pHist ln old /= pHist ln new) $ Map.keys old
  in concatMap (\ ln -> replicate (length' ln new - length' ln old) ln) changes

nodeErr :: Int -> IO ()
nodeErr descr = error $ "node with descriptor " ++ show descr
                ++ " has no corresponding node in the development graph"

showSpec :: Int -> DGraph -> IO ()
showSpec descr dgraph = do
  let sp = dgToSpec dgraph descr
      sp' = case sp of
              Res.Result ds Nothing -> showRelDiags 2 ds
              Res.Result _ m -> showDoc m ""
  createTextDisplay "Show spec" sp' [size(80,25)]

showNodeInfo :: Int -> DGraph -> IO ()
showNodeInfo descr dgraph = do
  let dgnode = labDG dgraph descr
      title = (if isDGRef dgnode then ("reference " ++) else
               if isInternalNode dgnode then ("internal " ++) else id)
              "node " ++ getDGNodeName dgnode ++ " " ++ show descr
  createTextDisplay title (title ++ "\n" ++ showDoc dgnode "")
    [HTk.size(70, 30)]

{- |
   fetches the theory from a node inside the IO Monad
   (added by KL based on code in getTheoryOfNode) -}
lookupTheoryOfNode :: IORef LibEnv -> LIB_NAME -> Int
                   -> IO (Res.Result (LibEnv, Node, G_theory))
lookupTheoryOfNode proofStatusRef ln descr = do
  libEnv <- readIORef proofStatusRef
  return $ do
    (libEnv', gth) <- computeTheory libEnv ln descr
    return (libEnv', descr, gth)

{- | outputs the theory of a node in a window;
used by the node menu defined in initializeGraph-}
getTheoryOfNode :: GInfo -> Int -> DGraph -> IO ()
getTheoryOfNode gInfo@(GInfo { gi_LIB_NAME = ln
                             , gi_GraphInfo = actGraphInfo
                             , libEnvIORef = le
                             }) descr dgraph = do
 r <- lookupTheoryOfNode le ln descr
 case r of
  Res.Result ds res -> do
    showDiags (gi_hetcatsOpts gInfo) ds
    case res of
      (Just (le', n, gth)) -> do
        lockGlobal gInfo
        GUI.HTkUtils.displayTheoryWithWarning
                "Theory" (getNameOfNode n dgraph)
                (addHasInHidingWarning dgraph n)
                gth
        let newGr = lookupDGraph ln le'
            newHistory = proofHistory newGr
        libEnv <- readIORef le
        let oldHistory = proofHistory $ lookupDGraph ln libEnv
            history = take (length newHistory - length oldHistory) newHistory
        applyChanges actGraphInfo history
        writeIORef le le'
        unlockGlobal gInfo
      _ -> return ()

{- | translate the theory of a node in a window;
used by the node menu defined in initializeGraph-}
translateTheoryOfNode :: GInfo -> Int -> DGraph -> IO ()
translateTheoryOfNode gInfo@(GInfo {gi_hetcatsOpts = opts,
                                    libEnvIORef = le})
                      descr dgraph = do
 libEnv <- readIORef le
 case (do
   (libEnv', th) <- computeTheory libEnv (gi_LIB_NAME gInfo) descr
   return (libEnv', descr,th) ) of
  Res.Result [] (Just (_le', node, th)) -> do
    Res.Result ds _ <-  runResultT(
      do G_theory lid sign _ sens _ <- return th
         -- find all comorphism paths starting from lid
         let paths = findComorphismPaths logicGraph (sublogicOfTh th)
         -- let the user choose one
         sel <- lift $ listBox "Choose a logic translation"
                   (map show paths)
         i <- case sel of
           Just j -> return j
           _ -> liftR $ fail "no logic translation chosen"
         Comorphism cid <- return (paths!!i)
         -- adjust lid's
         let lidS = sourceLogic cid
             lidT = targetLogic cid
         sign' <- coerceSign lid lidS "" sign
         sens' <- coerceThSens lid lidS "" sens
         -- translate theory along chosen comorphism
         (sign'',sens1) <-
             liftR $ wrapMapTheory cid (plainSign sign', toNamedList sens')
         lift $ GUI.HTkUtils.displayTheoryWithWarning
                "Translated Theory" (getNameOfNode node dgraph)
                (addHasInHidingWarning dgraph node)
                (G_theory lidT (mkExtSign sign'') startSigId
                 (toThSens sens1) startThId)
     )
    showDiags opts ds
    return ()
  Res.Result ds _ -> showDiags opts ds

-- | Show proof status of a node
showProofStatusOfNode :: GInfo -> Int -> DGraph -> IO ()
showProofStatusOfNode _ descr dgraph = do
  let dgnode = labDG dgraph descr
      stat = showStatusAux dgnode
      title =  "Proof status of node "++showName (dgn_name dgnode)
  createTextDisplay title stat [HTk.size(105,55)]

showStatusAux :: DGNodeLab -> String
showStatusAux dgnode =
  case dgn_theory dgnode of
  G_theory _ _ _ sens _ ->
     let goals = OMap.filter (not . isAxiom) sens
         (proven,open) = OMap.partition isProvenSenStatus goals
         consGoal = "\nconservativity of this node"
      in "Proven proof goals:\n"
         ++ showDoc proven ""
         ++ if not $ hasOpenConsStatus True dgnode
             then consGoal
             else ""
         ++ "\nOpen proof goals:\n"
         ++ showDoc open ""
         ++ if hasOpenConsStatus False dgnode
             then consGoal
             else ""

-- | start local theorem proving or consistency checking at a node
proveAtNode :: Bool -> GInfo -> Int -> DGraph -> IO ()
proveAtNode checkCons gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                                   , gi_LIB_NAME = ln }) descr dgraph = do
  let dgn = labDG dgraph descr
      libNode = (ln,descr)
  (dgraph',dgn') <- case hasLock dgn of
    True -> return (dgraph, dgn)
    False -> do
      lockGlobal gInfo
      le <- readIORef ioRefProofStatus
      (dgraph',dgn') <- initLocking (lookupDGraph ln le) (descr, dgn)
      writeIORef ioRefProofStatus $ Map.insert ln dgraph' le
      unlockGlobal gInfo
      return (dgraph',dgn')
  locked <- tryLockLocal dgn'
  case locked of
    False -> do
      createTextDisplay "Error" "Proofwindow already open" [HTk.size(30,10)]
    True -> do
      let action = do
            le <- readIORef ioRefProofStatus
            guiMVar <- newMVar Nothing
            res <- basicInferenceNode checkCons logicGraph libNode ln
                guiMVar le
            runProveAtNode gInfo (descr, dgn') res
      case checkCons || not (hasIncomingHidingEdge dgraph' $ snd libNode) of
        True -> action
        False -> GUI.HTkUtils.createInfoDisplayWithTwoButtons "Warning"
                   "This node has incoming hiding links!!!" "Prove anyway"
                   action
  unlockLocal dgn'

runProveAtNode :: GInfo -> LNode DGNodeLab
               -> Res.Result (LibEnv, Res.Result G_theory) -> IO ()
runProveAtNode gInfo (v, dgnode) res = case maybeResult res of
    Just (le, tres) -> do
        case maybeResult tres of
          Just gth -> createTextSaveDisplay
            ("Model for " ++ getDGNodeName dgnode ++ " node: " ++ show v)
            "model.log"  $ showDoc gth ""
          Nothing -> case diags tres of
            [] -> return ()
            ds ->
              createTextDisplay "Error" (showRelDiags 2 ds) [HTk.size(50,10)]
        proofMenu gInfo $ mergeDGNodeLab gInfo
          (v, labDG (lookupDGraph (gi_LIB_NAME gInfo) le) v)
    Nothing -> return ()

mergeDGNodeLab :: GInfo -> LNode DGNodeLab -> LibEnv -> IO (Res.Result LibEnv)
mergeDGNodeLab (GInfo{gi_LIB_NAME = ln}) (v, new_dgn) le = do
  let dg = lookupDGraph ln le
      old_dgn = labDG dg v
  return $ do
    theory <- joinG_sentences (dgn_theory old_dgn) $ dgn_theory new_dgn
    let new_dgn' = old_dgn { dgn_theory = theory }
        (dg', _) = labelNodeDG (v, new_dgn') dg
        dg'' = addToProofHistoryDG ([], [SetNodeLab old_dgn (v, new_dgn')]) dg'
    return $ Map.insert ln dg'' le

-- | print the id, origin, type, proof-status and morphism of the edge
showEdgeInfo :: Int -> Maybe (LEdge DGLinkLab) -> IO ()
showEdgeInfo descr me = case me of
  Just e@(_, _, l) -> let estr = showLEdge e in
    createTextDisplay ("Info of " ++ estr)
      (estr ++ "\n" ++ showDoc l "") [HTk.size(70,30)]
  Nothing -> createTextDisplay "Error"
    ("edge " ++ show descr ++ " has no corresponding edge"
     ++ "in the development graph") [HTk.size(50,10)]

-- | check conservativity of the edge
checkconservativityOfEdge :: Int -> GInfo -> Maybe (LEdge DGLinkLab) -> IO ()
checkconservativityOfEdge _ gInfo
                           (Just (source,target,linklab)) = do
  libEnv <- readIORef $ libEnvIORef gInfo
  let dgraph = lookupDGraph (gi_LIB_NAME gInfo) libEnv
      dgtar = labDG dgraph target
  if isDGRef dgtar then error "checkconservativityOfEdge: no DGNode" else do
      G_theory lid _ _ sens _ <- return $ dgn_theory dgtar
      GMorphism cid _ _ morphism2 _ <- return $ dgl_morphism linklab
      morphism2' <- coerceMorphism (targetLogic cid) lid
                   "checkconservativityOfEdge" morphism2
      let (_le', th) = case computeTheory libEnv (gi_LIB_NAME gInfo) source of
                Res.Result _ (Just th1) -> th1
                _ -> error "checkconservativityOfEdge: computeTheory"
      G_theory lid1 sign1 _ sens1 _ <- return th
      sign2 <- coerceSign lid1 lid "checkconservativityOfEdge.coerceSign" sign1
      sens2 <- coerceThSens lid1 lid "" sens1
      let Res.Result ds res =
              conservativityCheck lid
                 (plainSign sign2, toNamedList sens2)
                 morphism2' $ toNamedList sens
          showRes = case res of
                     Just (Just Inconsistent) -> "The link is not conservative"
                     Just (Just Conservative) -> "The link is conservative"
                     Just (Just Monomorphic) -> "The link is monomorphic"
                     Just (Just Definitional) -> "The link is definitional"
                     _ -> "Could not determine whether link is conservative"
              --     Just(Just True) -> "The link is conservative"
              --     Just(Just False) -> "The link is not conservative"
              --     _ -> "Could not determine whether link is conservative"
          myDiags = showRelDiags 2 ds
      createTextDisplay "Result of conservativity check"
                      (showRes ++ "\n" ++ myDiags) [HTk.size(50,50)]

checkconservativityOfEdge descr _ Nothing =
      createTextDisplay "Error"
          ("edge " ++ show descr ++ " has no corresponding edge "
                ++ "in the development graph") [HTk.size(30,10)]

-- | converts a DGraph
convert :: GA.GraphInfo -> DGraph -> IO ()
convert ginfo dgraph = do
  convertNodes ginfo dgraph
  convertEdges ginfo dgraph

{- | converts the nodes of the development graph, if it has any,
and returns the resulting conversion maps
if the graph is empty the conversion maps are returned unchanged-}
convertNodes :: GA.GraphInfo -> DGraph -> IO ()
convertNodes ginfo = mapM_ (convertNodesAux ginfo) .labNodesDG

{- | auxiliary function for convertNodes if the given list of nodes is
emtpy, it returns the conversion maps unchanged otherwise it adds the
converted first node to the abstract graph and to the affected
conversion maps and afterwards calls itself with the remaining node
list -}
convertNodesAux :: GA.GraphInfo -> LNode DGNodeLab -> IO ()
convertNodesAux ginfo (node, dgnode) =
  GA.addNode ginfo node (getRealDGNodeType dgnode) $ getDGNodeName dgnode

{- | converts the edges of the development graph
works the same way as convertNods does-}
convertEdges :: GA.GraphInfo -> DGraph -> IO ()
convertEdges ginfo = mapM_ (convertEdgesAux ginfo) . labEdgesDG

-- | auxiliary function for convertEges
convertEdgesAux :: GA.GraphInfo -> LEdge DGLinkLab -> IO ()
convertEdgesAux ginfo e@(src, tar, lbl) =
  GA.addEdge ginfo (dgl_id lbl) (getRealDGLinkType lbl) src tar "" $ Just e

-- | show library referened by a DGRef node (=node drawn as a box)
showReferencedLibrary :: Int -> GInfo -> ConvFunc -> LibFunc -> IO ()
showReferencedLibrary descr gInfo@(GInfo { libEnvIORef = ioRefProofStatus
                                         , gi_LIB_NAME = ln })
                      convGraph showLib = do
  le <- readIORef ioRefProofStatus
  let refNode =  labDG (lookupDGraph ln le) descr
      refLibname = if isDGRef refNode then dgn_libname refNode
                   else error "showReferencedLibrary"
  case Map.lookup refLibname le of
    Just _ -> do
      gInfo' <- copyGInfo gInfo refLibname
      convGraph gInfo' "development graph" showLib
      let gv = gi_GraphInfo gInfo'
      GA.deactivateGraphWindow gv
      hideNodes gInfo'
      GA.redisplay gv
      GA.layoutImproveAll gv
      GA.showTemporaryMessage gv "Development Graph initialized."
      GA.activateGraphWindow gv
      return ()
    Nothing -> error $ "The referenced library (" ++ show refLibname
                       ++ ") is unknown"

-- | apply the changes of first history item (computed by proof rules,
-- see folder Proofs) to the displayed development graph
applyChanges :: GA.GraphInfo -> ProofHistory -> IO ()
applyChanges _ [] = return ()
applyChanges ginfo ((_, hElem) : _) = mapM_ (applyChangesAux ginfo)
  $ removeContraryChanges hElem

-- | auxiliary function for applyChanges
applyChangesAux :: GA.GraphInfo -> DGChange -> IO ()
applyChangesAux ginfo change =
  case change of
    SetNodeLab _ (node, newLab) ->
      GA.changeNodeType ginfo node $ getRealDGNodeType newLab
    InsertNode (node, nodelab) ->
      GA.addNode ginfo node (getRealDGNodeType nodelab) $ getDGNodeName nodelab
    DeleteNode (node, _) ->
      GA.delNode ginfo node
    InsertEdge e@(src, tgt, lbl) ->
      GA.addEdge ginfo (dgl_id lbl) (getRealDGLinkType lbl) src tgt "" $ Just e
    DeleteEdge (_, _, lbl) ->
      GA.delEdge ginfo $ dgl_id lbl

-- | display a window of translated graph with maximal sublogic.
openTranslateGraph :: LibEnv -> LIB_NAME -> HetcatsOpts
                   -> Res.Result G_sublogics -> ConvFunc -> LibFunc -> IO ()
openTranslateGraph libEnv ln opts (Res.Result diagsSl mSublogic) convGraph
  showLib =
    -- if an error existed by the search of maximal sublogicn
    -- (see GUI.DGTranslation.getDGLogic), the process need not to go on.
    let myErrMess = errorMess . showRelDiags (verbose opts) in
    if hasErrors diagsSl then myErrMess diagsSl
       else case mSublogic of
             Just sublogic -> do
                 let paths = findComorphismPaths logicGraph sublogic
                 if null paths then
                     errorMess "This graph has no comorphism to translation."
                   else do
                       Res.Result diagsR i <- runResultT ( do
                         -- the user choose one
                         sel <- lift $ listBox "Choose a logic translation"
                                (map show paths)
                         case sel of
                           Just j -> return j
                           _ -> liftR $ fail "no logic translation chosen")
                       let aComor = paths !! fromJust i
                       -- graph translation.
                       case libEnv_translation libEnv aComor of
                         Res.Result diagsTrans (Just newLibEnv) -> do
                             showDiags opts (diagsSl ++ diagsR ++ diagsTrans)
                             if hasErrors (diagsR ++ diagsTrans) then
                                    myErrMess $ diagsR ++ diagsTrans
                                  else dg_showGraphAux
                                   (\gI@(GInfo{libEnvIORef = iorLE}) -> do
                                     writeIORef iorLE newLibEnv
                                     convGraph (gI{ gi_LIB_NAME = ln
                                                  , gi_hetcatsOpts = opts})
                                               "translation Graph" showLib)
                         Res.Result diagsTrans Nothing ->
                             myErrMess $ diagsSl ++ diagsR ++ diagsTrans
             Nothing -> errorMess "the maximal sublogic is not found."

dg_showGraphAux :: (GInfo -> IO ()) -> IO ()
dg_showGraphAux convFct = do
  useHTk    -- All messages are displayed in TK dialog windows
            -- from this point on
  gInfo <- emptyGInfo
  convFct gInfo
  let actGraphInfo = gi_GraphInfo gInfo
  GA.deactivateGraphWindow actGraphInfo
  GA.redisplay actGraphInfo
  GA.layoutImproveAll actGraphInfo
  GA.activateGraphWindow actGraphInfo

-- DaVinciGraph to String
-- Functions to convert a DaVinciGraph to a String to store as a .udg file

-- | saves the uDrawGraph graph to a file
saveUDGraph :: GInfo -> Map.Map DGNodeType (Shape value, String)
            -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String) -> IO ()
saveUDGraph gInfo@(GInfo { gi_GraphInfo = graphInfo
                         , gi_LIB_NAME = ln
                         , gi_hetcatsOpts = opts
                         }) nodemap linkmap = do
  evnt <- newFileDialogStr "Save as..."
                           $ (rmSuffix $ libNameToFile opts ln) ++ ".udg"
  maybeFilePath <- HTk.sync evnt
  case maybeFilePath of
    Just filepath -> do
      GA.showTemporaryMessage graphInfo "Converting graph..."
      nstring <- nodes2String gInfo nodemap linkmap
      writeFile filepath nstring
      GA.showTemporaryMessage graphInfo $ "Graph stored to " ++ filepath ++ "!"
    Nothing -> GA.showTemporaryMessage graphInfo $ "Aborted!"


-- | Converts the nodes of the graph to String representation
nodes2String :: GInfo -> Map.Map DGNodeType (Shape value, String)
             -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
             -> IO String
nodes2String gInfo@(GInfo { gi_GraphInfo = graphInfo
                          , gi_LIB_NAME = ln
                          , libEnvIORef = ioRefProofStatus
                          }) nodemap linkmap = do
  le <- readIORef ioRefProofStatus
  nodes <- filterM (\(n,_) -> do b <- GA.isHiddenNode graphInfo n
                                 return $ not b)
                    $ labNodesDG $ lookupDGraph ln le
  nstring <- foldM (\s node -> do
                     s' <- (node2String gInfo nodemap linkmap node)
                     return $ s ++ (if s /= "" then ",\n " else "") ++ s')
                   "" nodes
  return $ "[" ++ nstring ++ "]"

-- | Converts a node to String representation
node2String :: GInfo -> Map.Map DGNodeType (Shape value, String)
            -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
            -> LNode DGNodeLab -> IO String
node2String gInfo nodemap linkmap (nid, dgnode) = do
  label <- getNodeLabel gInfo dgnode
  let ntype = getRealDGNodeType dgnode
  (shape, color) <- case Map.lookup ntype nodemap of
    Nothing -> error $ "SaveGraph: can't lookup nodetype: " ++ show ntype
    Just (s, c) -> return (s, c)
  let
    object = "a(\"OBJECT\",\"" ++ label ++ "\"),"
    color' = "a(\"COLOR\",\"" ++ color ++ "\"),"
    shape' = "a(\"_GO\",\"" ++ (map toLower $ show shape) ++ "\")"
  links  <- links2String gInfo linkmap nid
  return $ "l(\"" ++ (show nid) ++ "\",n(\"" ++ show ntype ++ "\","
           ++ "[" ++ object ++ color' ++ shape' ++ "],"
           ++ "\n  [" ++ links ++ "]))"

-- | Converts all links of a node to String representation
links2String :: GInfo -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
             -> Int -> IO String
links2String (GInfo { gi_GraphInfo = graphInfo
                    , gi_LIB_NAME = ln
                    , libEnvIORef = ioRefProofStatus
                    })  linkmap nodeid = do
  le <- readIORef ioRefProofStatus
  edges <- filterM (\(src,_,edge) -> do
                      let eid = dgl_id edge
                      b <- GA.isHiddenEdge graphInfo eid
                      return $ (not b) && src == nodeid)
                     $ labEdgesDG $ lookupDGraph ln le
  foldM (\s edge -> do
          s' <- link2String linkmap edge
          return $ s ++ (if s /= "" then ",\n   " else "") ++ s') "" edges

-- | Converts a link to String representation
link2String :: Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
            -> LEdge DGLinkLab -> IO String
link2String linkmap (nodeid1, nodeid2, edge) = do
  let (EdgeId linkid) = dgl_id edge
      ltype = getRealDGLinkType edge
  (line, color) <- case Map.lookup ltype linkmap of
    Nothing -> error $ "SaveGraph: can't lookup linktype: " ++ show ltype
    Just (l, c) -> return (l, c)
  let
    name   = "\"" ++ (show linkid) ++ ":" ++ (show nodeid1) ++ "->"
             ++ (show nodeid2) ++ "\""
    color' = "a(\"EDGECOLOR\",\"" ++ color ++ "\"),"
    line'  = "a(\"EDGEPATTERN\",\"" ++ (map toLower $ show line) ++ "\")"
  return $ "l(" ++ name ++ ",e(\"" ++ show ltype ++ "\","
           ++ "[" ++ color' ++ line' ++"],"
           ++ "r(\"" ++ (show nodeid2) ++ "\")))"

-- | Returns the name of the Node
getNodeLabel :: GInfo -> DGNodeLab -> IO String
getNodeLabel (GInfo {internalNamesIORef = ioRefInternal}) dgnode = do
  internal <- readIORef ioRefInternal
  let ntype = getDGNodeType dgnode
  return $ if (not $ showNames internal) &&
       elem ntype ["open_cons__internal"
                  , "proven_cons__internal"
                  , "locallyEmpty__open_cons__internal"
                  , "locallyEmpty__proven_cons__internal"]
           then "" else getDGNodeName dgnode
