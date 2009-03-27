{-# OPTIONS -cpp #-}
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
    , performProofAction
    , openProofStatus
    , saveProofStatus
    , nodeErr
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
    , checkconservativityOfEdge
    , convert
    , hideNodes
    , hideNewProvedEdges
    , hideShowNames
    , showNodes
    , translateGraph
    , showLibGraph
    , runAndLock
    , saveUDGraph
    , focusNode
    , applyChanges
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

import Proofs.EdgeUtils
import Proofs.InferBasic(basicInferenceNode)
import Proofs.StatusUtils(lookupHistory, removeContraryChanges)
import Proofs.TheoremHideShift

import GUI.Taxonomy (displayConceptGraph,displaySubsortGraph)
import GUI.GraphTypes
import qualified GUI.GraphAbstraction as GA
import GUI.Utils

#ifdef UNIVERSION2
import Graphs.GraphConfigure
import Reactor.InfoBus(encapsulateWaitTermAct)
#else
import GraphConfigure
import InfoBus(encapsulateWaitTermAct)
#endif
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
      GA.deactivateGraphWindow gi
      function
      takeMVar lock
      GA.redisplay gi
      GA.layoutImproveAll gi
      GA.activateGraphWindow gi
    False ->
      GA.showTemporaryMessage gi
        "an other function is still working ... please wait ..."

-- | Undo one step of the History
undo :: GInfo -> Bool -> IO ()
undo gInfo@(GInfo { graphInfo = gi }) isUndo = do
  hhn <- GA.hasHiddenNodes gi
  intSt <- readIORef $ intState gInfo
  nwSt <- if isUndo then undoOneStep intSt else redoOneStep intSt
  writeIORef (intState gInfo) nwSt
  if hhn then hideNodes gInfo else return ()
  GA.redisplay gi

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
showNodes gInfo@(GInfo { graphInfo = gi
                       }) = do
  hhn <- GA.hasHiddenNodes gi
  case hhn of
    True -> do
      GA.showTemporaryMessage gi "Revealing hidden nodes ..."
      GA.showAll gi
      hideShowNames gInfo False
    False ->
      GA.showTemporaryMessage gi "No hidden nodes found ..."

-- | hides all unnamed internal nodes that are proven
hideNodes :: GInfo -> IO ()
hideNodes gInfo@(GInfo { graphInfo = gi
                       , libName = ln }) = do
  hhn <- GA.hasHiddenNodes gi
  ost <- readIORef $ intState gInfo
  case i_state ost of
   Nothing -> return ()
   Just ist -> if hhn then
       GA.showTemporaryMessage gi "Nodes already hidden ..."
     else do
       GA.showTemporaryMessage gi "Hiding unnamed nodes..."
       let le = i_libEnv ist
           dg = lookupDGraph ln le
           nodes = selectNodesByType dg [DGNodeType
                                          { nonRefType = NonRefType
                                            { isProvenCons = True
                                            , isInternalSpec = True}
                                          , isLocallyEmpty = True}]
           edges = getCompressedEdges dg nodes
       GA.hideNodes gi nodes edges

-- | hides all proven edges created not initialy
hideNewProvedEdges :: GInfo -> IO ()
hideNewProvedEdges gInfo@(GInfo { graphInfo = gi
                                , libName = ln }) = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
   Nothing -> return ()
   Just ist -> do
     let ph = SizedList.toList $ proofHistory
                               $ lookupDGraph ln $ i_libEnv ist
         edges = foldl (\ e c -> case c of
                         InsertEdge (_, _, lbl) -> (dgl_id lbl):e
                         DeleteEdge (_, _, lbl) -> delete (dgl_id lbl) e
                         _ -> e
                       ) [] $ flattenHistory ph []
     mapM_ (GA.hideEdge gi) edges
     GA.redisplay gi

-- | generates from list of HistElem one list of DGChanges
flattenHistory :: [HistElem] -> [DGChange] -> [DGChange]
flattenHistory [] cs = cs
flattenHistory ((HistElem c):r) cs = flattenHistory r $ c:cs
flattenHistory ((HistGroup _ ph):r) cs =
  flattenHistory r $ flattenHistory (SizedList.toList ph) cs

-- | selects all nodes of a type with outgoing edges
selectNodesByType :: DGraph -> [DGNodeType] -> [Node]
selectNodesByType dg types =
  filter (\ n -> outDG dg n /= []) $ map fst
         $ filter (\ (_, n) -> elem (getRealDGNodeType n) types) $ labNodesDG dg

-- | compresses a list of types to the highest one
compressTypes :: Bool -> [DGEdgeType] -> (DGEdgeType, Bool)
compressTypes _ [] = error "compressTypes: wrong usage"
compressTypes b (t:[]) = (t,b)
compressTypes b (t1:t2:r) = if t1 == t2 then compressTypes b (t1:r) else
  if t1 > t2 then compressTypes False (t1:r) else compressTypes False (t2:r)

-- | returns a list of compressed edges
getCompressedEdges :: DGraph -> [Node] -> [(Node,Node,(DGEdgeType, Bool))]
getCompressedEdges dg hidden = filterDuplicates $ getShortPaths
  $ concatMap (\ e@(_,t,_) -> map (e:) $ getPaths dg t hidden []) inEdges
  where
    inEdges = filter (\ (_,t,_) -> elem t hidden)
                     $ concatMap (outDG dg)
                     $ foldr (\ n i -> if elem n hidden
                                       || elem n i then i else n:i) []
                     $ map (\ (s,_,_) -> s) $ concatMap (innDG dg) hidden

-- | filter duplicate paths
filterDuplicates :: [(Node,Node,(DGEdgeType, Bool))]
                 -> [(Node,Node,(DGEdgeType, Bool))]
filterDuplicates [] = []
filterDuplicates ((s, t, (et,b)) : r) = edge : filterDuplicates others
  where
    (same,others) = partition (\ (s',t',_) -> s == s' && t == t') r
    b' = and $ b : map (\ (_,_,(_,b'')) -> b'') same
    edge = (s,t,compressTypes b' $ et : map (\ (_,_,(et',_)) -> et') same)

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
              -> [(Node,Node,(DGEdgeType,Bool))]
getShortPaths [] = []
getShortPaths (p : r) =
  (s, t, compressTypes True $ map (\ (_,_,e) -> getRealDGLinkType e) p)
    : getShortPaths r
  where
    (s,_,_) = head p
    (_,t,_) = last p

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

{- | it tries to perform the given action to the given graph.
     If part of the given graph is not hidden, then the action can
     be performed directly; otherwise the graph will be shown completely
     firstly, and then the action will be performed, and after that the graph
     will be hidden again.
-}
performProofAction :: GInfo -> IO () -> IO ()
performProofAction gInfo@(GInfo { graphInfo = gi
                                }) proofAction = do
  let actionWithMessage = do
          GA.showTemporaryMessage gi
               "Applying development graph calculus proof rule..."
          proofAction
  hhn  <- GA.hasHiddenNodes gi
  case hhn of
    True -> do
      showNodes gInfo
      actionWithMessage
      hideNodes gInfo
    False -> actionWithMessage
  GA.showTemporaryMessage gi
                       "Development graph calculus proof rule finished."

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
    mh <- readVerbose opts ln file
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
             -> String
             -> (LibEnv -> IO (Result LibEnv))
             -> IO ()
proofMenu gInfo@(GInfo { graphInfo = gi
                       , hetcatsOpts = hOpts
                       , proofGUIMVar = guiMVar
                       , libName = ln
                       }) str proofFun = do
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
              nmStr = strToCmd str
              nst = add2history nmStr ost lln
              nwst = nst { i_state = Just ist { i_libEnv=newProofStatus}}
          doDump hOpts "PrintHistory" $ do
            putStrLn "History"
            print $ prettyHistory history
          applyChanges gi $ reverse $ flatHistory history
          writeIORef (intState gInfo) nwst
          unlockGlobal gInfo
          hideShowNames gInfo False
          mGUIMVar <- tryTakeMVar guiMVar
          maybe (fail "should be filled with Nothing after proof attempt")
                (const $ return ())
                mGUIMVar

calcGlobalHistory :: LibEnv -> LibEnv -> [LIB_NAME]
calcGlobalHistory old new = let
    length' ln = SizedList.size . proofHistory . lookupDGraph ln
    changes = filter (\ ln -> length' ln old < length' ln new) $ Map.keys old
  in concatMap (\ ln -> replicate (length' ln new - length' ln old) ln) changes

nodeErr :: Int -> IO ()
nodeErr descr = error $ "node with descriptor " ++ show descr
                ++ " has no corresponding node in the development graph"

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
            guiMVar <- newMVar Nothing
            res <- basicInferenceNode checkCons logicGraph ln dgraph'
              (descr, dgn') guiMVar le' iSt
            runProveAtNode checkCons gInfo (descr, dgn') res
            unlockLocal dgn'
      if checkCons && labelHasHiding dgn' then do
          b <- warningDialog "Warning"
             (unwords $ hidingWarning ++ ["Try anyway?"]) $ Just action
          unless b $ unlockLocal dgn'
          return ()
        else forkIO action >> return ()
    else errorDialog "Error" "Proofwindow already open"

runProveAtNode :: Bool -> GInfo -> LNode DGNodeLab
               -> Result G_theory -> IO ()
runProveAtNode checkCons gInfo (v, dgnode) (Result ds mres) =
    if checkCons then do
        let nodetext = getDGNodeName dgnode ++ " node: " ++ show v
        case mres of
          Just gth -> createTextSaveDisplay ("Model for " ++ nodetext)
                                            "model.log" $ showDoc gth ""
          Nothing -> infoDialog nodetext $ unlines
            $ "could not (re-)construct a" : "model" : map diagString ds
    else let oldTh = dgn_theory dgnode in case mres of
       Just newTh | newTh /= oldTh -> do
         let Result es tres = joinG_sentences oldTh newTh
             ln = libName gInfo
             iSt = intState gInfo
         showDiagMessAux 2 $ ds ++ es
         case tres of
           Just theory -> do
             lockGlobal gInfo
             ost <- readIORef iSt
             case i_state ost of
               Nothing -> unlockGlobal gInfo
               Just iist -> do
                 let le = i_libEnv iist
                     dgraph = lookupDGraph ln le
                     new_dgn = dgnode { dgn_theory = theory }
                     newDg = changeDGH dgraph $ SetNodeLab dgnode (v, new_dgn)
                     history = snd $ splitHistory dgraph newDg
                     nst = add2history "" ost [DgCommandChange ln]
                     nwst = nst
                       { i_state = Just iist
                         { i_libEnv = Map.insert ln newDg le } }
                 applyChanges (graphInfo gInfo) $ reverse $ flatHistory history
                 writeIORef iSt nwst
                 unlockGlobal gInfo
                 hideShowNames gInfo False
           Nothing -> return ()
       _ -> return ()

-- | print the id, origin, type, proof-status and morphism of the edge
showEdgeInfo :: Int -> Maybe (LEdge DGLinkLab) -> IO ()
showEdgeInfo descr me = case me of
  Just e@(_, _, l) -> let estr = showLEdge e in
    createTextDisplay ("Info of " ++ estr)
      (estr ++ "\n" ++ showDoc l "")
  Nothing -> errorDialog "Error"
    ("edge " ++ show descr ++ " has no corresponding edge"
     ++ "in the development graph")

-- | check conservativity of the edge
checkconservativityOfEdge :: Int -> GInfo -> Maybe (LEdge DGLinkLab) -> IO ()
checkconservativityOfEdge _ gInfo@(GInfo{ graphInfo = gi
                                        , libName = ln })
                          (Just (source,target,linklab)) = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
    let libEnv' = i_libEnv ist
    lockGlobal gInfo
    (str,nwle,ph)<-checkConservativityEdge True (source,target,linklab)
                        libEnv' ln
    case isPrefixOf "No conservativity" str of
     True ->do
             errorDialog "Result of conservativity check" str
             unlockGlobal gInfo
     False -> do
               createTextDisplay "Result of conservativity check" str
               applyChanges gi $ reverse $ flatHistory ph
               GA.redisplay gi
               let nwst = ost { i_state = Just $ ist { i_libEnv = nwle}}
               writeIORef (intState gInfo) nwst
               unlockGlobal gInfo

checkconservativityOfEdge descr _ Nothing =
      errorDialog "Error"
          ("edge " ++ show descr ++ " has no corresponding edge "
                ++ "in the development graph")
{-
conservativityRule :: DGRule
conservativityRule = DGRule "ConservativityCheck"

-- | Graphical choser for conservativity checkers
conservativityChoser :: [ConservativityChecker sign sentence morphism]
                     -> IO
                         (Result (ConservativityChecker
                          sign sentence morphism))
conservativityChoser checkers = case checkers of
      [] -> return $ fail "No conservativity checkers available"
      [hd] -> return $ return hd
      _ ->
          do
            chosenOne <- listBox "Pick a conservativity checker"
                         $ map checker_id checkers
            case chosenOne of
              Nothing -> return $ fail "No conservativity checker chosen"
              Just i  -> return $ return $ checkers !! i
-}

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
      GA.deactivateGraphWindow gi
      hideNodes gInfo'
      GA.redisplay gi
      GA.layoutImproveAll gi
      GA.showTemporaryMessage gi "Development Graph initialized."
      GA.activateGraphWindow gi
      return ()
    Nothing -> error $ "The referenced library (" ++ show refLibname
                       ++ ") is unknown"

-- | apply the changes of first history item (computed by proof rules,
-- see folder Proofs) to the displayed development graph
applyChanges :: GA.GraphInfo -> [DGChange] -> IO ()
applyChanges ginfo = mapM_ (applyChangesAux ginfo) . removeContraryChanges

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
getNodeLabel (GInfo {internalNamesIORef = ioRefInternal}) dgnode = do
  internal <- readIORef ioRefInternal
  let ntype = getDGNodeType dgnode
  return $ if (not $ showNames internal) &&
       elem ntype ["open_cons__internal"
                  , "proven_cons__internal"
                  , "locallyEmpty__open_cons__internal"
                  , "locallyEmpty__proven_cons__internal"]
           then "" else getDGNodeName dgnode
