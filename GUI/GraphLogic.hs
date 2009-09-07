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
    , updateGraph
    , openProofStatus
    , saveProofStatus
    , proofMenu
    , showReferencedLibrary
    , getTheoryOfNode
    , translateTheoryOfNode
    , displaySubsortGraph
    , displayConceptGraph
    , showProofStatusOfNode
    , proveAtNode
    , showNodeInfo
    , showDiagMess
    , showEdgeInfo
    , checkconservativityOfNode
    , checkconservativityOfEdge
    , toggleHideNames
    , toggleHideNodes
    , toggleHideEdges
    , translateGraph
    , showLibGraph
    , runAndLock
    , saveUDGraph
    , focusNode
    ) where

import Logic.Coerce(coerceSign)
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover
import Comorphisms.LogicGraph(logicGraph)

import Static.GTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.DGTranslation(libEnv_translation, getDGLogic)

import Proofs.ComputeTheory
import Proofs.EdgeUtils
import Proofs.InferBasic(basicInferenceNode)
import Proofs.StatusUtils(lookupHistory, removeContraryChanges)

import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)
import GUI.GraphTypes
import qualified GUI.GraphAbstraction as GA
import GUI.Utils

import Graphs.GraphConfigure
import Reactor.InfoBus(encapsulateWaitTermAct)
import qualified GUI.HTkUtils as HTk

import Common.DocUtils (showDoc)
import Common.AS_Annotation (isAxiom)
import Common.ExtSign
import Common.LibName
import Common.Result
import qualified Common.OrderedMap as OMap
import qualified Common.Lib.SizedList as SizedList

import Driver.Options(HetcatsOpts,putIfVerbose,outtypes,doDump,verbose,rmSuffix)
import Driver.WriteLibDefn(writeShATermFile)
import Driver.ReadFn(libNameToFile, readVerbose)
import Driver.AnaLib(anaLib)

import Data.IORef
import Data.Char(toLower)
import Data.List(partition, delete, isPrefixOf)
import Data.Maybe
import Data.Graph.Inductive.Graph (Node, LEdge, LNode)
import qualified Data.Map as Map

import Control.Monad
import Control.Concurrent (forkIO)
import Control.Concurrent.MVar

import Interfaces.Command
import Interfaces.History
import Interfaces.DataTypes
import Interfaces.Utils

-- | Locks the global lock and runs function
runAndLock :: GInfo -> IO () -> IO ()
runAndLock (GInfo { functionLock = lock
                  , graphInfo = gi
                  }) function = do
  locked <- tryPutMVar lock ()
  case locked of
    True -> do
      function
      takeMVar lock
    False ->
      GA.showTemporaryMessage gi
        "an other function is still working ... please wait ..."

-- | Undo one step of the History
undo :: GInfo -> Bool -> IO ()
undo gInfo isUndo = do
  intSt <- readIORef $ intState gInfo
  nwSt <- if isUndo then undoOneStepWithUpdate intSt $ updateGraphAux gInfo
                    else redoOneStepWithUpdate intSt $ updateGraphAux gInfo
  writeIORef (intState gInfo) nwSt

updateGraph :: GInfo -> [DGChange] -> IO ()
updateGraph gInfo@(GInfo { libName = ln }) changes = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
    Nothing -> return ()
    Just ist -> updateGraphAux gInfo ln changes $ lookupDGraph ln $ i_libEnv ist

updateGraphAux :: GInfo -> LIB_NAME -> [DGChange] -> DGraph -> IO ()
updateGraphAux gInfo' ln changes dg = do
  og <- readIORef $ openGraphs gInfo'
  case Map.lookup ln og of
    Nothing -> return ()
    Just gInfo@(GInfo { graphInfo = gi
                      , options = opts }) -> do
      flags <- readIORef opts
      let (nodes, comp) = if flagHideNodes flags then hideNodesAux dg
                          else ([],[])
          edges = if flagHideEdges flags then hideEdgesAux dg else []
      GA.showTemporaryMessage gi
        "Applying development graph calculus proof rule..."
      GA.deactivateGraphWindow gi
      GA.applyChanges gi (removeContraryChanges changes) nodes edges comp
      GA.showTemporaryMessage gi
        "Updating graph..."
      GA.redisplay gi
      hideNames gInfo
      GA.layoutImproveAll gi
      GA.activateGraphWindow gi
      GA.showTemporaryMessage gi
        "Development graph calculus proof rule finished."

-- | Toggles to display internal node names
hideNames :: GInfo -> IO ()
hideNames (GInfo { options = opts
                 , internalNames = updaterIORef }) = do
  flags <- readIORef opts
  updater <- readIORef updaterIORef
  mapM_ (\(s,upd) -> upd (\_ -> if flagHideNames flags then "" else s)) updater

-- | Toggles to display internal node names
toggleHideNames :: GInfo -> IO ()
toggleHideNames gInfo@(GInfo { graphInfo = gi
                             , options = opts }) = do
  flags <- readIORef opts
  let hide = not $ flagHideNames flags
  writeIORef opts $ flags { flagHideNames = hide }
  GA.showTemporaryMessage gi $ if hide then "Hiding internal names..."
                               else "Revealing internal names..."
  updateGraph gInfo []

-- | hides all unnamed internal nodes that are proven
hideNodesAux :: DGraph
             -> ([GA.NodeId], [(GA.NodeId, GA.NodeId, DGEdgeType, Bool)])
hideNodesAux dg =
  let nodes = selectNodesByType dg [DGNodeType { nonRefType = NonRefType
                                                 { isProvenCons = True
                                                 , isInternalSpec = True}
                                               , isLocallyEmpty = True}]
      edges = getCompressedEdges dg nodes
  in (nodes, edges)

toggleHideNodes :: GInfo -> IO ()
toggleHideNodes gInfo@(GInfo { graphInfo = gi
                             , options = opts }) = do
  flags <- readIORef opts
  let hide = not $ flagHideNodes flags
  writeIORef opts $ flags { flagHideNodes = hide }
  GA.showTemporaryMessage gi $ if hide then "Hiding unnamed nodes..."
                               else "Revealing hidden nodes..."
  updateGraph gInfo []

hideEdgesAux :: DGraph -> [EdgeId]
hideEdgesAux dg = map dgl_id
  $ filter (\ (DGLink { dgl_type = linktype }) ->
             case linktype of
               ScopedLink _ (ThmLink s) c ->
                 isProvenThmLinkStatus s && isProvenConsStatusLink c
               HidingFreeOrCofreeThm _ _ s -> isProvenThmLinkStatus s
               _ -> False
           )
  $ foldl (\ e c -> case c of
                      InsertEdge (_, _, lbl) -> lbl:e
                      DeleteEdge (_, _, lbl) -> delete lbl e
                      _ -> e
          ) [] $ flattenHistory (SizedList.toList $ proofHistory dg) []

toggleHideEdges :: GInfo -> IO ()
toggleHideEdges gInfo@(GInfo { graphInfo = gi
                             , options = opts }) = do
  flags <- readIORef opts
  let hide = not $ flagHideEdges flags
  writeIORef opts $ flags { flagHideEdges = hide }
  GA.showTemporaryMessage gi $ if hide then "Hiding new proven edges..."
                               else "Revealing hidden proven edges..."
  updateGraph gInfo []

-- | generates from list of HistElem one list of DGChanges
flattenHistory :: [HistElem] -> [DGChange] -> [DGChange]
flattenHistory [] cs = cs
flattenHistory ((HistElem c):r) cs = flattenHistory r $ c:cs
flattenHistory ((HistGroup _ ph):r) cs =
  flattenHistory r $ flattenHistory (SizedList.toList ph) cs

-- | selects all nodes of a type with outgoing edges
selectNodesByType :: DGraph -> [DGNodeType] -> [Node]
selectNodesByType dg types = filter (\ n -> outDG dg n /= []) $ map fst
  $ filter (\ (_, n) -> elem (getRealDGNodeType n) types) $ labNodesDG dg

-- | compresses a list of types to the highest one
compressTypes :: Bool -> [DGEdgeType] -> (DGEdgeType, Bool)
compressTypes _ [] = error "compressTypes: wrong usage"
compressTypes b (t:[]) = (t,b)
compressTypes b (t1:t2:r) = if t1 == t2 then compressTypes b (t1:r) else
  if t1 > t2 then compressTypes False (t1:r) else compressTypes False (t2:r)

-- | returns a list of compressed edges
getCompressedEdges :: DGraph -> [Node] -> [(Node,Node,DGEdgeType, Bool)]
getCompressedEdges dg hidden = filterDuplicates $ getShortPaths
  $ concatMap (\ e@(_,t,_) -> map (e:) $ getPaths dg t hidden []) inEdges
  where
    inEdges = filter (\ (_,t,_) -> elem t hidden)
                     $ concatMap (outDG dg)
                     $ foldr (\ n i -> if elem n hidden
                                       || elem n i then i else n:i) []
                     $ map (\ (s,_,_) -> s) $ concatMap (innDG dg) hidden

-- | filter duplicate paths
filterDuplicates :: [(Node,Node,DGEdgeType, Bool)]
                 -> [(Node,Node,DGEdgeType, Bool)]
filterDuplicates [] = []
filterDuplicates r@((s, t, _, _) : _) = edges ++ filterDuplicates others
  where
    (same,others) = partition (\ (s',t', _, _) -> s == s' && t == t') r
    (mtypes,stypes) = partition (\ (_,_,_,b) -> not b) same
    stypes' = foldr (\e es -> if elem e es then es else e:es) [] stypes
    (et',_) = compressTypes False $ map (\ (_,_,et,_) -> et) mtypes
    edges = if length mtypes /= 0 then (s,t,et',False):stypes' else stypes'

-- | returns the pahts of a given node through hidden nodes
getPaths :: DGraph -> Node -> [Node] -> [Node] -> [[LEdge DGLinkLab]]
getPaths dg node hidden seen' = case elem node hidden of
  True -> case edges /= [] of
    True -> concatMap (\ e@(_,t,_) -> map (e:) $ getPaths dg t hidden seen)
                         edges
    False -> []
  False -> [[]]
  where
    seen = node:seen'
    edges = filter (\ (_,t,_) -> notElem t seen) $ outDG dg node

-- | returns source and target node of a path with the compressed type
getShortPaths :: [[LEdge DGLinkLab]]
              -> [(Node,Node,DGEdgeType,Bool)]
getShortPaths [] = []
getShortPaths (p : r) =
  (s, t, et, b)
    : getShortPaths r
  where
    (s,_,_) = head p
    (_,t,_) = last p
    (et, b) = compressTypes True $ map (\ (_,_,e) -> getRealDGLinkType e) p

-- | Let the user select a Node to focus
focusNode :: GInfo -> IO ()
focusNode gInfo@(GInfo { graphInfo = gi
                       , libName = ln }) = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let le = i_libEnv ist
   idsnodes <- filterM (fmap not . GA.isHiddenNode gi . fst)
                    $ labNodesDG $ lookupDGraph ln le
   selection <- listBox "Select a node to focus"
     $ map (\ (n, l) -> shows n " " ++ getDGNodeName l) idsnodes
   case selection of
    Just idx -> GA.focusNode gi $ fst $ idsnodes !! idx
    Nothing -> return ()

showLibGraph :: GInfo -> LibFunc -> IO ()
showLibGraph gInfo showLib = do
  showLib gInfo
  return ()

saveProofStatus :: GInfo -> FilePath -> IO ()
saveProofStatus gInfo@(GInfo { hetcatsOpts = opts
                             , libName = ln
                             }) file = encapsulateWaitTermAct $ do
  ost <- readIORef $ intState gInfo
  case i_state ost of
   Nothing -> return ()
   Just ist -> do
    let proofStatus = i_libEnv ist
    writeShATermFile file (ln, lookupHistory ln proofStatus)
    putIfVerbose opts 2 $ "Wrote " ++ file

-- | implementation of open menu, read in a proof status
openProofStatus :: GInfo -> FilePath -> ConvFunc -> LibFunc
                -> IO ()
openProofStatus gInfo@(GInfo { hetcatsOpts = opts
                             , libName = ln }) file convGraph showLib = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
    mh <- readVerbose logicGraph opts ln file
    case mh of
      Nothing -> errorDialog "Error" $ "Could not read proof status from file '"
                               ++ file ++ "'"
      Just h -> do
          let libfile = libNameToFile opts ln
          m <- anaLib opts { outtypes = [] } libfile
          case m of
            Nothing -> errorDialog "Error"
                         $ "Could not read original development graph from '"
                           ++ libfile ++  "'"
            Just (_, libEnv) -> case Map.lookup ln libEnv of
                Nothing -> errorDialog "Error" $ "Could not get original"
                             ++ "development graph for '" ++ showDoc ln "'"
                Just dg -> do
                    lockGlobal gInfo
                    let oldEnv = i_libEnv ist
                        proofStatus = Map.insert ln
                                      (applyProofHistory h dg) oldEnv
                        nwst = ost { i_state = Just ist {
                                      i_libEnv = proofStatus } }
                    writeIORef (intState gInfo) nwst
                    unlockGlobal gInfo
                    gInfo' <- copyGInfo gInfo ln
                    convGraph gInfo' "Proof Status " showLib
                    let gi = graphInfo gInfo
                    GA.deactivateGraphWindow gi
                    GA.redisplay gi
                    GA.layoutImproveAll gi
                    GA.activateGraphWindow gi

-- | apply a rule of the development graph calculus
proofMenu :: GInfo
             -> Command
             -> (LibEnv -> IO (Result LibEnv))
             -> IO ()
proofMenu gInfo@(GInfo { hetcatsOpts = hOpts
                       , proofGUIMVar = guiMVar
                       , libName = ln
                       }) cmd proofFun = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   filled <- tryPutMVar guiMVar Nothing
   if not filled
    then readMVar guiMVar >>=
                  maybe (putIfVerbose hOpts 0 "proofMenu: ignored Nothing")
                         (\ w -> do
                             putIfVerbose hOpts 4 $
                                  "proofMenu: Ignored Proof command; " ++
                                  "maybe a proof window is still open?"
                             HTk.putWinOnTop w)
    else do
      lockGlobal gInfo
      let proofStatus = i_libEnv ist
      putIfVerbose hOpts 4 "Proof started via menu"
      Result ds res <- proofFun proofStatus
      putIfVerbose hOpts 4 "Analyzing result of proof"
      case res of
        Nothing -> do
          unlockGlobal gInfo
          printDiags 2 ds
        Just newProofStatus -> do
          let newGr = lookupDGraph ln newProofStatus
              history = snd $ splitHistory (lookupDGraph ln proofStatus) newGr
              lln = map DgCommandChange $ calcGlobalHistory
                                                   proofStatus newProofStatus
              nst = add2history cmd ost lln
              nwst = nst { i_state = Just ist { i_libEnv=newProofStatus}}
          doDump hOpts "PrintHistory" $ do
            putStrLn "History"
            print $ prettyHistory history
          writeIORef (intState gInfo) nwst
          updateGraph gInfo (reverse $ flatHistory history)
          unlockGlobal gInfo
          mGUIMVar <- tryTakeMVar guiMVar
          maybe (fail "should be filled with Nothing after proof attempt")
                (const $ return ())
                mGUIMVar

calcGlobalHistory :: LibEnv -> LibEnv -> [LIB_NAME]
calcGlobalHistory old new = let
    length' ln = SizedList.size . proofHistory . lookupDGraph ln
    changes = filter (\ ln -> length' ln old < length' ln new) $ Map.keys old
  in concatMap (\ ln -> replicate (length' ln new - length' ln old) ln) changes

showNodeInfo :: Int -> DGraph -> IO ()
showNodeInfo descr dgraph = do
  let dgnode = labDG dgraph descr
      title = (if isDGRef dgnode then ("reference " ++) else
               if isInternalNode dgnode then ("internal " ++) else id)
              "node " ++ getDGNodeName dgnode ++ " " ++ show descr
  createTextDisplay title (title ++ "\n" ++ showDoc dgnode "")

showDiagMessAux :: Int -> [Diagnosis] -> IO ()
showDiagMessAux v ds = let es = filterDiags v ds in
  if null es then return () else
  (if hasErrors es then errorDialog "Error" else infoDialog "Info") $ unlines
     $ map show es

showDiagMess :: HetcatsOpts -> [Diagnosis] -> IO ()
showDiagMess = showDiagMessAux . verbose

{- | outputs the theory of a node in a window;
     used by the node menu -}
getTheoryOfNode :: GInfo -> Int -> DGraph -> IO ()
getTheoryOfNode gInfo descr dgraph = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
    let Result ds res = computeTheory (i_libEnv ist) (libName gInfo) descr
    showDiagMess (hetcatsOpts gInfo) ds
    maybe (return ())
        (displayTheoryWithWarning "Theory" (getNameOfNode descr dgraph)
        $ addHasInHidingWarning dgraph descr) res

{- | translate the theory of a node in a window;
     used by the node menu -}
translateTheoryOfNode :: GInfo -> Int -> DGraph -> IO ()
translateTheoryOfNode gInfo@(GInfo { hetcatsOpts = opts
                                   , libName = ln }) node dgraph = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
    let libEnv = i_libEnv ist
        Result ds moTh = computeTheory libEnv ln node
    case moTh of
      Just th@(G_theory lid sign _ sens _) -> do
         -- find all comorphism paths starting from lid
         let paths = findComorphismPaths logicGraph (sublogicOfTh th)
         -- let the user choose one
         sel <- listBox "Choose a node logic translation" $ map show paths
         case sel of
           Nothing -> errorDialog "Error" "no node logic translation chosen"
           Just i -> do
             Comorphism cid <- return (paths!!i)
             -- adjust lid's
             let lidS = sourceLogic cid
                 lidT = targetLogic cid
             sign' <- coerceSign lid lidS "" sign
             sens' <- coerceThSens lid lidS "" sens
             -- translate theory along chosen comorphism
             let Result es mTh = wrapMapTheory cid
                   (plainSign sign', toNamedList sens')
             case mTh of
               Nothing -> showDiagMess opts es
               Just (sign'', sens1) -> displayTheoryWithWarning
                "Translated Theory" (getNameOfNode node dgraph)
                (addHasInHidingWarning dgraph node)
                (G_theory lidT (mkExtSign sign'') startSigId
                 (toThSens sens1) startThId)
      Nothing -> showDiagMess opts ds

-- | Show proof status of a node
showProofStatusOfNode :: GInfo -> Int -> DGraph -> IO ()
showProofStatusOfNode _ descr dgraph = do
  let dgnode = labDG dgraph descr
      stat = showStatusAux dgnode
      title =  "Proof status of node "++showName (dgn_name dgnode)
  createTextDisplay title stat

showStatusAux :: DGNodeLab -> String
showStatusAux dgnode =
  case dgn_theory dgnode of
  G_theory _ _ _ sens _ ->
     let goals = OMap.filter (not . isAxiom) sens
         (proven,open) = OMap.partition isProvenSenStatus goals
         consGoal = "\nconservativity of this node"
      in "Proven proof goals:\n"
         ++ showDoc proven ""
         ++ if not $ hasOpenNodeConsStatus True dgnode
             then consGoal
             else ""
         ++ "\nOpen proof goals:\n"
         ++ showDoc open ""
         ++ if hasOpenNodeConsStatus False dgnode
             then consGoal
             else ""

hidingWarnDiag :: DGNodeLab -> IO () -> IO ()
hidingWarnDiag dgn action =
      if labelHasHiding dgn then do
          warningDialog "Warning"
             (unwords $ hidingWarning ++ ["Try anyway?"]) $ Just action
          return ()
        else forkIO action >> return ()

-- | start local theorem proving or consistency checking at a node
proveAtNode :: Bool -> GInfo -> Int -> DGraph -> IO ()
proveAtNode checkCons gInfo descr dgraph = do
 let ln = libName gInfo
     iSt = intState gInfo
 ost <- readIORef iSt
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let le = i_libEnv ist
       dgn = labDG dgraph descr
   (dgraph', dgn', le') <- if hasLock dgn then return (dgraph, dgn, le) else do
      lockGlobal gInfo
      (dgraph', dgn') <- initLocking (lookupDGraph ln le) (descr, dgn)
      let nwle = Map.insert ln dgraph' le
          nwst = ost { i_state = Just $ ist { i_libEnv = nwle} }
      writeIORef iSt nwst
      unlockGlobal gInfo
      return (dgraph', dgn', nwle)
   acquired <- tryLockLocal dgn'
   if acquired then do
      let action = do
            res@(Result d _) <- basicInferenceNode checkCons logicGraph ln
                                   dgraph' (descr, dgn') le' iSt
            if hasErrors d && (diagString $ d !! 0) == "Proofs.Proofs: selection"
              then return ()
              else runProveAtNode checkCons gInfo (descr, dgn') res
      hidingWarnDiag dgn' action
      unlockLocal dgn'
    else errorDialog "Error" "Proofwindow already open"

runProveAtNode :: Bool -> GInfo -> LNode DGNodeLab
               -> Result G_theory -> IO ()
runProveAtNode checkCons gInfo (v, dgnode) (Result ds mres) =
     let nn = getDGNodeName dgnode in
     if checkCons then do
        let nodetext = nn ++ " node: " ++ show v
        case mres of
          Just gth -> do
            createTextSaveDisplay ("Model for " ++ nodetext)
                                            "model.log" $ showDoc gth ""
            updateNodeProof checkCons gInfo (v, dgnode) mres
          Nothing -> infoDialog nodetext $ unlines
            $ "could not (re-)construct a" : "model" : map diagString ds
    else let oldTh = dgn_theory dgnode in case mres of
       Just newTh | newTh /= oldTh -> do
         let Result es tres = joinG_sentences oldTh newTh
         showDiagMessAux 2 $ ds ++ es
         updateNodeProof checkCons gInfo (v, dgnode) tres
       _ -> return ()

updateNodeProof :: Bool -> GInfo -> LNode DGNodeLab -> Maybe G_theory -> IO ()
updateNodeProof checkCons gInfo (v, dgnode) tres = case tres of
  Just theory -> do
    let ln = libName gInfo
        iSt = intState gInfo
        nn = getDGNodeName dgnode
    lockGlobal gInfo
    ost <- readIORef iSt
    case i_state ost of
      Nothing -> return ()
      Just iist -> do
        let le = i_libEnv iist
            dgraph = lookupDGraph ln le
            new_dgn = if checkCons then dgnode
                { nodeInfo = case nodeInfo dgnode of
                    ninfo@DGNode { node_cons_status = ConsStatus c _ _ } ->
                        ninfo { node_cons_status = ConsStatus c Cons
                                $ Proven (DGRule "ConsistencyChecker")
                                emptyProofBasis }
                    ninfo -> ninfo }
                else dgnode { dgn_theory = theory }
            newDg = changeDGH dgraph $ SetNodeLab dgnode (v, new_dgn)
            history = snd $ splitHistory dgraph newDg
            nst = add2history
                       (CommentCmd $ "basic inference done on " ++ nn ++ "\n")
                           ost [DgCommandChange ln]
            nwst = nst
                       { i_state = Just iist
                         { i_libEnv = Map.insert ln newDg le } }
        writeIORef iSt nwst
        runAndLock gInfo $ updateGraph gInfo $ reverse $ flatHistory history
    unlockGlobal gInfo
  Nothing -> return ()

checkconservativityOfNode :: Int -> GInfo -> DGraph -> IO ()
checkconservativityOfNode descr gInfo dgraph = do
  let iSt = intState gInfo
      ln = libName gInfo
      nlbl = labDG dgraph descr
  ost <- readIORef iSt
  case i_state ost of
    Nothing -> return ()
    Just iist -> hidingWarnDiag nlbl $ do
      lockGlobal gInfo
      (str, libEnv', ph) <- checkConservativityNode True
                            (descr, nlbl) (i_libEnv iist) ln
      if isPrefixOf "No conservativity" str
        then
          errorDialog "Result of conservativity check" str
        else do
          createTextDisplay "Result of conservativity check" str
          let nst = add2history (SelectCmd Node $ showDoc descr "")
                    ost [DgCommandChange ln]
              nwst = nst { i_state = Just $ iist { i_libEnv = libEnv' }}
          writeIORef iSt nwst
          runAndLock gInfo $ updateGraph gInfo (reverse $ flatHistory ph)
      unlockGlobal gInfo

edgeErr :: Int -> IO ()
edgeErr descr = errorDialog "Error" $ "edge with descriptor " ++ show descr
                ++ " not found in the development graph"

-- | print the id, origin, type, proof-status and morphism of the edge
showEdgeInfo :: Int -> Maybe (LEdge DGLinkLab) -> IO ()
showEdgeInfo descr me = case me of
  Just e@(_, _, l) -> let estr = showLEdge e in
    createTextDisplay ("Info of " ++ estr)
      (estr ++ "\n" ++ showDoc l "")
  Nothing -> edgeErr descr

-- | check conservativity of the edge
checkconservativityOfEdge :: Int -> GInfo -> Maybe (LEdge DGLinkLab) -> IO ()
checkconservativityOfEdge descr gInfo me = case me of
    Nothing -> edgeErr descr
    Just lnk@(_, _, lbl) -> do
      let iSt = intState gInfo
          ln = libName gInfo
      ost <- readIORef iSt
      case i_state ost of
        Nothing -> return ()
        Just iist -> do
          lockGlobal gInfo
          (str, nwle, ph) <- checkConservativityEdge True lnk (i_libEnv iist) ln
          if isPrefixOf "No conservativity" str
            then
              errorDialog "Result of conservativity check" str
            else do
              createTextDisplay "Result of conservativity check" str
              let nst = add2history (SelectCmd Link $ showDoc (dgl_id lbl) "")
                        ost [DgCommandChange ln]
                  nwst = nst { i_state = Just $ iist { i_libEnv = nwle}}
              writeIORef iSt nwst
              runAndLock gInfo $ updateGraph gInfo $ reverse $ flatHistory ph
          unlockGlobal gInfo

-- | show library referened by a DGRef node (=node drawn as a box)
showReferencedLibrary :: Int -> GInfo -> ConvFunc -> LibFunc -> IO ()
showReferencedLibrary descr gInfo@(GInfo{ libName = ln })
                      convGraph showLib = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let le = i_libEnv ist
       refNode =  labDG (lookupDGraph ln le) descr
       refLibname = if isDGRef refNode then dgn_libname refNode
                    else error "showReferencedLibrary"
   case Map.lookup refLibname le of
    Just _ -> do
      gInfo' <- copyGInfo gInfo refLibname
      convGraph gInfo' "development graph" showLib
      let gi = graphInfo gInfo'
      GA.showTemporaryMessage gi "Development Graph initialized."
    Nothing -> error $ "The referenced library (" ++ show refLibname
                       ++ ") is unknown"

-- | display a window of translated graph with maximal sublogic.
translateGraph :: GInfo -> IO (Maybe LibEnv)
translateGraph gInfo@(GInfo { hetcatsOpts = opts }) = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
    Nothing -> return Nothing
    Just ist -> do
      let
        le = i_libEnv ist
        Result diagsSl mSublogic = getDGLogic le
        myErrMess = showDiagMess opts
        error' = errorDialog "Error"
      if hasErrors diagsSl then do
          myErrMess diagsSl
          return Nothing
        else case mSublogic of
          Nothing -> do
            error' "No maximal sublogic found."
            return Nothing
          Just sublogic -> do
            let paths = findComorphismPaths logicGraph sublogic
            if null paths then do
                error' "This graph has no comorphism to translation."
                return Nothing
              else do
                sel <- listBox "Choose a logic translation" $ map show paths
                case sel of
                  Nothing -> do
                    error' "no logic translation chosen"
                    return Nothing
                  Just j -> do
                    let Result diag mle = libEnv_translation le $ paths !! j
                    case mle of
                      Just newLibEnv -> do
                        showDiagMess opts $ diagsSl ++ diag
                        return $ Just newLibEnv
                      Nothing -> do
                        myErrMess $ diagsSl ++ diag
                        return Nothing

-- DaVinciGraph to String
-- Functions to convert a DaVinciGraph to a String to store as a .udg file

-- | saves the uDrawGraph graph to a file
saveUDGraph :: GInfo -> Map.Map DGNodeType (Shape value, String)
            -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String) -> IO ()
saveUDGraph gInfo@(GInfo { graphInfo = gi
                         , hetcatsOpts = opts
                         , libName = ln }) nodemap linkmap = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
   Nothing -> return ()
   Just _ -> do
    maybeFilePath <- fileSaveDialog ((rmSuffix $ libNameToFile opts ln)
                                     ++ ".udg")
                                  [ ("uDrawGraph",["*.udg"])
                                  , ("All Files", ["*"])] Nothing
    case maybeFilePath of
     Just filepath -> do
      GA.showTemporaryMessage gi "Converting graph..."
      nstring <- nodes2String gInfo nodemap linkmap
      writeFile filepath nstring
      GA.showTemporaryMessage gi $ "Graph stored to " ++ filepath ++ "!"
     Nothing -> GA.showTemporaryMessage gi "Aborted!"

-- | Converts the nodes of the graph to String representation
nodes2String :: GInfo -> Map.Map DGNodeType (Shape value, String)
             -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
             -> IO String
nodes2String gInfo@(GInfo { graphInfo = gi
                          , libName = ln  }) nodemap linkmap = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return []
  Just ist -> do
   let le = i_libEnv ist
   nodes <- filterM (\(n,_) -> do b <- GA.isHiddenNode gi n
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
    shape' = "a(\"_GO\",\"" ++ map toLower (show shape) ++ "\")"
  links  <- links2String gInfo linkmap nid
  return $ "l(\"" ++ show nid ++ "\",n(\"" ++ show ntype ++ "\","
           ++ "[" ++ object ++ color' ++ shape' ++ "],"
           ++ "\n  [" ++ links ++ "]))"

-- | Converts all links of a node to String representation
links2String :: GInfo -> Map.Map DGEdgeType (EdgePattern GA.EdgeValue, String)
             -> Int -> IO String
links2String gInfo@(GInfo { graphInfo = gi
                          , libName = ln })  linkmap nodeid = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return []
  Just ist -> do
   let le = i_libEnv ist
   edges <- filterM (\ (src, _, edge) -> do
     let eid = dgl_id edge
     b <- GA.isHiddenEdge gi eid
     return $ not b && src == nodeid)
       $ labEdgesDG $ lookupDGraph ln le
   foldM (\ s edge -> do
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
    nm   = "\"" ++ show linkid ++ ":" ++ show nodeid1 ++ "->"
             ++ show nodeid2 ++ "\""
    color' = "a(\"EDGECOLOR\",\"" ++ color ++ "\"),"
    line'  = "a(\"EDGEPATTERN\",\"" ++ map toLower (show line) ++ "\")"
  return $ "l(" ++ nm ++ ",e(\"" ++ show ltype ++ "\","
           ++ "[" ++ color' ++ line' ++"],"
           ++ "r(\"" ++ show nodeid2 ++ "\")))"

-- | Returns the name of the Node
getNodeLabel :: GInfo -> DGNodeLab -> IO String
getNodeLabel (GInfo { options = opts }) dgnode = do
  flags <- readIORef opts
  return $ if flagHideNames flags && isInternalNode dgnode
           then "" else getDGNodeName dgnode
