{- |
Module      :  $Header$
Description :  theorem hide shift proof rule for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

theorem hide shift proof rule for development graphs
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.
-}

module Proofs.TheoremHideShift
    ( theoremHideShift
    , theoremHideShiftFromList
    , convertToNf
    , hasIngoingHidingDef
    , computeTheory
    , computeLocalTheory
    , theoremsToAxioms
    ) where

import Data.List (partition)

import Logic.Logic
import Logic.Prover

import Static.GTheory
import Static.DevGraph
import Static.WACocone(GDiagram)
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map

import Syntax.AS_Library
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.ComputeColimit

import Control.Monad
import Data.List(nub, sortBy)

import Proofs.SimpleTheoremHideShift(getInComingGlobalUnprovenEdges)
import Common.Id

-- normal forms

{- | converts the given node to its own normal form -}
convertToNf :: LIB_NAME -> LibEnv -> Node -> Result LibEnv
convertToNf ln libEnv node = do
  let dgraph = lookupDGraph ln libEnv
      nodelab = labDG dgraph node
  case dgn_nf nodelab of
    -- here checks if it's already been computed
    Just _ -> return libEnv
    Nothing ->
     case isDGRef nodelab of
       True ->
               -- the normal form of the node
               -- is a reference to the normal form of the node it references
               -- careful: here not refNf, but a new Node which references refN

        let refLib = dgn_libname nodelab
            refNode = dgn_node nodelab
        in case (hasIngoingHidingDef libEnv refLib refNode) of
         True -> do
           libEnv' <- convertToNf refLib libEnv refNode
           let
            refGraph' = lookupDGraph (dgn_libname nodelab) libEnv'
            Just refNf = dgn_nf $ labDG refGraph' $ dgn_node nodelab
               -- the normal form just computed ^
            refNodelab = labDG refGraph' refNf
               -- the label of the normal form ^
            nfNode = getNewNodeDG dgraph
               -- the new reference node in the old graph ^
            NodeName tt ss _ = dgn_name nodelab
            nfName = mkSimpleId $ "NormalForm" ++ show tt ++ show node
            refLab = DGNodeLab{
                   dgn_name = NodeName nfName ss 0,
                   dgn_theory  = dgn_theory $ refNodelab,
                   dgn_nf = Just nfNode,
                   dgn_sigma = Just $ ide $ dgn_sign refNodelab,
                   nodeInfo = DGRef{ref_libname = dgn_libname nodelab,
                                    ref_node = refNf},
                   dgn_lock = Nothing
                  }
            newLab = nodelab{
                   dgn_nf = Just nfNode,
                   dgn_sigma = dgn_sigma $ labDG refGraph' $ dgn_node nodelab
                  }
            chLab = SetNodeLab nodelab (node, newLab)
            changes = [InsertNode (nfNode,refLab), chLab]
            (newGraph, changes') = updateWithChanges changes dgraph
         -- i should also collect the changes made in the referenced graph
         -- for undo
            allChanges = [([NormalForm],changes')]
            newProofStatus = mkResultProofStatus ln libEnv' newGraph
                       (concatMap fst allChanges, concatMap snd allChanges)
        --print $ prettyLibEnv newProofStatus
           return newProofStatus
         False -> do -- normal form is the node itself
          let
              newLab =  nodelab{
                          dgn_nf = Just node,
                          dgn_sigma = Just $ ide $ dgn_sign nodelab}
              chLab = SetNodeLab nodelab (node, newLab)
              changes = [([NormalForm],[chLab])]
              newGraph  = changeDG dgraph chLab
          return $ mkResultProofStatus ln libEnv newGraph
           (concatMap fst changes, concatMap snd changes)
       False -> case (hasIngoingHidingDef libEnv ln node) of
         False -> -- no hiding, nf is the node itself
               -- we need to update the fields
               -- dgn_sign and dgn_nf of node
           do
          let (sign, mor) = (dgn_theory nodelab, Just $ ide $ dgn_sign nodelab)
              newLab = (newNodeLab (dgn_name nodelab) DGProof sign){
                          dgn_nf = Just node,
                          dgn_sigma = mor}
              chLab = SetNodeLab nodelab (node, newLab)
              changes = [([NormalForm],[chLab])]
              newGraph  = changeDG dgraph chLab
          return $ mkResultProofStatus ln libEnv newGraph
           (concatMap fst changes, concatMap snd changes)
         True -> do
          auxProofstatus <- createNfsForPredecessors ln libEnv node
          let (diagram, g) = computeDiagram ln auxProofstatus node
              Result _ds res = gWeaklyAmalgamableCocone diagram
          case res of
              Nothing -> -- do sequence $ map (putStrLn . show) diags
                          -- trace "amalgamability test failed" $
                          -- handleNonLeaves ln auxProofstatus list
                        fail "convert to normal form: can't compute cocone"
              Just (sign, mmap) -> do
               let
            -- the new node which will contain the normal form
                auxGraph = lookupDGraph ln auxProofstatus
                nfNode = getNewNodeDG auxGraph
            -- the label of the new node
                NodeName tt ss _ = dgn_name nodelab
                nfName = mkSimpleId $ "NormalForm" ++ show tt ++ show node
                nfLabel = DGNodeLab{
                       dgn_name = NodeName nfName ss 0,
                       dgn_theory = sign,
                       dgn_nf = Just nfNode, -- is its own nf
                       dgn_sigma =  Just $ ide $ signOf sign, -- id morphism
                       nodeInfo = DGNode{
                                     node_origin = DGProof,
                                     node_cons_status = Nothing
                                  },
                       dgn_lock = Nothing
                      }
            -- the new label for node
                newLab = (newNodeLab (dgn_name nodelab) DGProof
                                   (dgn_theory nodelab))
                     { dgn_nf = Just nfNode,
                       dgn_sigma = Just $ mmap Map.! (g Map.! node)
                     }
            -- add the nf to the label of node
                chLab = SetNodeLab nodelab (node, newLab)
            -- insert the new node and add edges from the predecessors
                insNNF = InsertNode (nfNode, nfLabel)
                makeEdge src tgt m = (src, tgt, DGLink { dgl_morphism = m
                                              , dgl_type = GlobalDef
                                              , dgl_origin = DGLinkProof
                                              , dgl_id = defaultEdgeId
                                              })
                insStrMor = map (\(x, f) -> InsertEdge $ makeEdge x
                                                         nfNode f) $ nub $
                            map (\(x,y) -> (g Map.! x, y)) $ Map.toList mmap
                allChanges = chLab:insNNF:insStrMor
                (newGraph, changes') = updateWithChanges allChanges auxGraph
                newHistory = [([NormalForm],changes')]
                oldHistory = proofHistory dgraph
                auxHistory = take ((length $ proofHistory auxGraph) -
                                    length oldHistory ) $
                             proofHistory auxGraph
                hist = (reverse auxHistory) ++ newHistory
               return $ mkResultProofStatus ln auxProofstatus newGraph
                 (concatMap fst hist, concatMap snd hist)


-- {- | converts the given node to its own normal form -}
-- convertToNf :: LIB_NAME -> LibEnv -> Node -> Result LibEnv
-- convertToNf ln proofstatus node = do
--   let dgraph = lookupDGraph ln proofstatus
--       nodelab = labDG dgraph node
--   case dgn_nf nodelab of
--     -- here checks if it's already been computed
--     Just _ -> return proofstatus
--     Nothing ->
--      case isDGRef nodelab of
--        True -> -- proofstatus
--                -- the normal form of the node
--                -- is a reference to the normal form of the node it references
--                -- careful: here not refNf, but a new Node which references refNf
--               do
--         pfs' <- convertToNf (dgn_libname nodelab) proofstatus
--                               (dgn_node nodelab)
--         let
--          refGraph' = lookupDGraph (dgn_libname nodelab) pfs'
--          Just refNf = dgn_nf $ labDG refGraph' $ dgn_node nodelab
--          -- the normal form just computed ^
--          refNodelab = labDG refGraph' refNf
--          -- the label of the normal form ^
--          nfNode = getNewNodeDG dgraph
--          -- the new reference node in the old graph ^
--          refLab = DGNodeLab{
--                    dgn_name = emptyNodeName,
--                    dgn_theory = dgn_theory $ refNodelab,
--                    dgn_nf = Just nfNode,
--                    dgn_sigma = Just $ ide $ dgn_sign refNodelab,
--                    nodeInfo = DGRef{ref_libname = dgn_libname nodelab,
--                                     ref_node = refNf},
--                    dgn_lock = Nothing
--                   }
--          newLab = nodelab{
--                    dgn_nf = Just nfNode,
--                    dgn_sigma = dgn_sigma $ labDG refGraph' $ dgn_node nodelab
--                   }
--          chLab = SetNodeLab nodelab (node, newLab)
--          changes = [InsertNode (nfNode,refLab), chLab]
--          (newGraph, changes') = updateWithChanges changes dgraph
--          -- i should also collect the changes made in the referenced graph
--          -- for undo
--          allChanges = [([NormalForm],changes')]
--          newProofStatus = mkResultProofStatus ln pfs' newGraph
--                        (concatMap fst allChanges, concatMap snd allChanges)
--         return newProofStatus
--        False -> case (hasIngoingHidingDef proofstatus ln node) of
--          False -> -- no hiding, nf is the node itself
--                -- we need to update the fields
--                -- dgn_sign and dgn_nf of node
--            do
--           let (sign, mor) = (dgn_theory nodelab, Just $ ide $ dgn_sign nodelab)
--               newLab = (newNodeLab (dgn_name nodelab) DGProof sign){
--                           dgn_nf = Just node,
--                           dgn_sigma = mor}
--               chLab = SetNodeLab nodelab (node, newLab)
--               changes = [([NormalForm],[chLab])]
--               newGraph  = changeDG dgraph chLab
--           return $ mkResultProofStatus ln proofstatus newGraph
--            (concatMap fst changes, concatMap snd changes)
--          True -> do
--           auxProofstatus <- createNfsForPredecessors ln proofstatus node
--           let (diagram, g) = computeDiagram ln auxProofstatus node
--           let Result _ds res = gWeaklyAmalgamableCocone diagram
--           case res of
--               Nothing -> -- do sequence $ map (putStrLn . show) diags
--                           -- trace "amalgamability test failed" $
--                           -- handleNonLeaves ln auxProofstatus list
--                         fail "convert to normal form: can't compute cocone"
--               Just (sign, mmap) -> do
--                let
--             -- the new node which will contain the normal form
--                 auxGraph = lookupDGraph ln auxProofstatus
--                 nfNode = getNewNodeDG auxGraph
--             -- the label of the new node
--                 nfLabel = DGNodeLab{
--                        dgn_name = emptyNodeName,
--                        dgn_theory = sign,
--                        dgn_nf = Just nfNode, -- is its own nf
--                        dgn_sigma =  Just $ ide $ signOf sign, -- id morphism
--                        nodeInfo = DGNode{
--                                      node_origin = DGProof,
--                                      node_cons_status = Nothing
--                                   },
--                        dgn_lock = Nothing
--                       }
--             -- the new label for node
--                 newLab = (newNodeLab (dgn_name nodelab) DGProof
--                                    (dgn_theory nodelab))
--                      { dgn_nf = Just nfNode,
--                        dgn_sigma = Just $ mmap Map.! (g Map.! node)
--                      }
--             -- add the nf to the label of node
--                 chLab = SetNodeLab nodelab (node, newLab)
--             -- insert the new node and add edges from the predecessors
--                 insNNF = InsertNode (nfNode, nfLabel)
--                 makeEdge src tgt m = (src, tgt, DGLink { dgl_morphism = m
--                                               , dgl_type = GlobalDef
--                                               , dgl_origin = DGLinkProof
--                                               , dgl_id = defaultEdgeId
--                                               })
--                 insStrMor = map (\(x, f) -> InsertEdge $ makeEdge x
--                                                          nfNode f) $ nub $
--                             map (\(x,y) -> (g Map.! x, y)) $ Map.toList mmap
--                 allChanges = chLab:insNNF:insStrMor
--                 (newGraph, changes') = updateWithChanges allChanges auxGraph
--                 newHistory = [([NormalForm],changes')]
--                 oldHistory = proofHistory dgraph
--                 auxHistory = take ((length $ proofHistory auxGraph) -
--                                     length oldHistory ) $
--                              proofHistory auxGraph
--                 hist = auxHistory ++ newHistory
--                return  $ mkResultProofStatus ln auxProofstatus newGraph
--                  (concatMap fst hist, concatMap snd hist)

{- | creates the normal forms of the predecessors of the given node
 -}
createNfsForPredecessors :: LIB_NAME -> LibEnv -> Node -> Result LibEnv
createNfsForPredecessors ln proofstatus node =
  foldM (convertToNf ln) proofstatus predecessors
  where
    dgraph = lookupDGraph ln proofstatus
    defInEdges =  [edge| edge@(src,_,_) <- innDG dgraph node,
                   liftE (liftOr isGlobalDef isHidingDef) edge
                   && node /= src]
    predecessors = [src| (src,_,_) <- defInEdges]


computeDiagram ::  LIB_NAME -> LibEnv
                   -> Node
                   -> (GDiagram, Map.Map Node Node) -- (D, G)
computeDiagram ln libEnv node =
 let dgraph = lookupDGraph ln libEnv
     defInEdges = [edge| edge@(src,_,_) <- innDG dgraph node,
                   liftE (liftOr isGlobalDef isHidingDef) edge
                   && node /= src]
     --careful, local links not added yet!
     morphEdge n (_, _, labl) = if isHidingDef $ dgl_type labl
                                then (node,n,(x, dgl_morphism labl))
                                else (n,node,(x, dgl_morphism labl))
                                where EdgeId x = dgl_id labl
     gd = insNode (node, dgn_theory $ labDG dgraph node) empty :: GDiagram
     addNodes = zip (newNodes (length defInEdges) gd) defInEdges
                 -- for each edge, add a new node
     g' = Map.insert node node $
          Map.fromList $ map (\(x, (y, _,_)) -> (x,y)) addNodes
           -- each new node nn has the signature of the node g(nn)

     newLNodes = map (\n -> (n, dgn_theory $ labDG dgraph $ g' Map.! n))
                      $ map fst addNodes
      -- if the node g(nn) is its own normal form, do nothing
      -- otherwise add to the graph the normal from and the
      -- structural morphism
     newLEdges = map (\(n, e) -> morphEdge n e) addNodes
     getNfNodes nflist gf nlist =
       case nlist of
        [] -> (nflist, gf)
        n : nlist' ->
          let nlab = labDG dgraph $ g' Map.! n in
          case dgn_nf nlab of
           Nothing -> getNfNodes nflist gf nlist'
                          -- nfs computed, so dont enter here
           Just n' ->
             if (g' Map.! n) == n' then
                -- node is its own normal form, add nothing
               getNfNodes nflist gf nlist'
                                   else
               --we have to insert the normal form in D as a new node
              let nn = node + (length defInEdges) + length nflist + 1
               -- look for a better solution here?
                  Just mor = dgn_sigma nlab
                  gf' = Map.insert nn n' gf
              in getNfNodes (((nn, dgn_theory $ labDG dgraph n'),
                             --new node, fails for DGRef^
                           (n, nn, (1, mor))
                             -- the edge  from node to the nf^
                            ):nflist) gf' nlist'
     (nfChanges, g'') = getNfNodes [] Map.empty $ map fst newLNodes
     g = Map.union g'' g'
     allNodes = newLNodes ++ (map fst nfChanges)
     allEdges = newLEdges ++ (map snd nfChanges)
     gd' = insEdges allEdges $ insNodes allNodes gd
 in (gd',g)

---------------------------------------------------------------------

-- theorem hide shift

theoremHideShift :: LIB_NAME -> LibEnv -> Result LibEnv
theoremHideShift ln proofStatus =
 theoremHideShiftAux ln proofStatus $ nodesDG $ lookupDGraph ln proofStatus


theoremHideShiftAux :: LIB_NAME -> LibEnv -> [Node] -> Result LibEnv
theoremHideShiftAux ln proofStatus nodeList = do
  auxProofstatus <- foldM (convertToNf ln) proofStatus $
                     nodesDG $ lookupDGraph ln proofStatus
  let
     oldGraph = lookupDGraph ln proofStatus
     oldHistory = proofHistory oldGraph
     auxGraph = lookupDGraph ln auxProofstatus
     auxHistory = proofHistory auxGraph
     nfHistory = take (length auxHistory - length oldHistory) auxHistory
     (nodesWHiding, _) = partition (hasIngoingHidingDef proofStatus ln) nodeList
     -- all nodes with incoming hiding links
     -- all the theorem links entering these nodes
     -- have to replaced by theorem links with the same origin
     -- but pointing to the normal form of the former target node
     ingoingEdges = concat $
                    map (getInComingGlobalUnprovenEdges auxGraph) nodesWHiding
     (_graph, changesTHS) = foldl theoremHideShiftForEdge (auxGraph, [])
                             ingoingEdges
     changes = (concat $ map snd $ reverse nfHistory) ++ changesTHS
     (newGraph, changes') = updateWithChanges changes oldGraph
     newHistory = [([TheoremHideShift], changes')]
     newProofStatus = mkResultProofStatus ln auxProofstatus newGraph
                       (concatMap fst newHistory, concatMap snd newHistory)
  return newProofStatus

theoremHideShiftForEdge :: (DGraph, [DGChange]) ->  LEdge DGLinkLab ->
                           (DGraph, [DGChange])
theoremHideShiftForEdge (dg, chList) edge@(source, target, edgeLab) =
  case maybeResult $ theoremHideShiftForEdgeAux dg edge of
   Nothing -> error "theoremHideShiftForEdgeAux"
   Just ((dg', pbasis),changes) -> let
    GlobalThm _ conservativity conservStatus = dgl_type edgeLab
    provenEdge = (source, target, edgeLab
        { dgl_type = GlobalThm (Proven TheoremHideShift pbasis)
            conservativity conservStatus
        , dgl_origin = DGLinkProof })
    (dg2, insC) = updateWithChanges [DeleteEdge edge, InsertEdge provenEdge]
                   dg'
                                   in (dg2, chList ++ changes ++ insC)

theoremHideShiftForEdgeAux :: DGraph -> LEdge DGLinkLab ->
                      Result ((DGraph, ProofBasis), [DGChange])
theoremHideShiftForEdgeAux dg (sn, tn, llab) = do
  let tlab = labDG dg tn
      Just nfNode = dgn_nf tlab
      phi = dgl_morphism llab
      Just muN = dgn_sigma tlab
  cmor <- comp phi muN
  let newEdge =(sn, nfNode, DGLink{
                 dgl_morphism = cmor,
                 dgl_type = GlobalThm LeftOpen None LeftOpen,
                 dgl_origin = DGLinkProof,
                 dgl_id = defaultEdgeId
               })
  case tryToGetEdge newEdge dg of
        Nothing -> let
          (newGraph, newChange) =
            updateWithOneChange (InsertEdge newEdge) dg
          finalEdge = case newChange of
            [InsertEdge final_e] -> final_e
            _ -> error "Proofs.Global.globDecompForOneEdgeAux"
          in return
              ((newGraph, addEdgeId emptyProofBasis $ getEdgeId finalEdge)
             , newChange)
        Just e -> return ((dg, addEdgeId emptyProofBasis $ getEdgeId e), [])

theoremHideShiftFromList :: LIB_NAME -> [LNode DGNodeLab]
                              -> LibEnv -> Result LibEnv
theoremHideShiftFromList ln ls proofStatus =
  theoremHideShiftAux ln proofStatus $ map fst ls

{- | returns True, if the given node has at least one directly or
   indirectly (ie via an ingoing path of GlobalDef edges)
   ingoing HidingDef edge. returns False otherwise
 -}
hasIngoingHidingDef :: LibEnv -> LIB_NAME -> Node -> Bool
hasIngoingHidingDef libEnv ln node =
 let dgraph = lookupDGraph ln libEnv
     nodelab = labDG dgraph node
 in
 if isDGRef nodelab then
   -- if the referenced node has incoming hiding links
   -- then the reference is also treated as with hiding
   let DGRef refLib refNode = nodeInfo nodelab
   in hasIngoingHidingDef libEnv refLib refNode
 else
  not (null hidingDefEdges)
   || or [hasIngoingHidingDef libEnv ln' nod | (ln',nod) <- next]
  where
    inGoingEdges = getAllIngoingEdges libEnv ln node
    hidingDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isHidingDef n]
    globalDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isGlobalDef n]
    next = [ (l, s) | (l, (s, _, _)) <- globalDefEdges ]

-- hasIngoingHidingDef :: LibEnv -> LIB_NAME -> Node -> Bool
-- hasIngoingHidingDef libEnv ln node =
--   not (null hidingDefEdges)
--    || or [hasIngoingHidingDef libEnv ln' nod | (ln',nod) <- next]
--   where
--     inGoingEdges = getAllIngoingEdges libEnv ln node
--     -- check for DGRef
--     hidingDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isHidingDef n]
--     globalDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isGlobalDef n]
--     next = [ (l, s) | (l, (s, _, _)) <- globalDefEdges ]
-- -- TO DO: check if this is enough ^

-- if a node N has incoming definition links from a DGRef node,
-- we should not care if the referenced node has or not incoming hiding links
-- so the node N should not be thought of as having incoming hiding links
-- this is whats is going on in RCCVerification example
-- the problem is - why the referenced node has incoming hiding links?

getAllIngoingEdges :: LibEnv -> LIB_NAME -> Node
                   -> [(LIB_NAME, LEdge DGLinkLab)]
getAllIngoingEdges libEnv ln node = inEdgesInThisGraph
  --case isDGRef nodelab of
  --  False -> inEdgesInThisGraph
  --  True -> inEdgesInThisGraph -- ++ inEdgesInRefGraph
  where
    dgraph = lookupDGraph ln libEnv
    -- nodelab = labDG dgraph node
    inEdgesInThisGraph = [(ln,inEdge)| inEdge <- innDG dgraph node]
    -- refLn = dgn_libname nodelab
--     refGraph = lookupDGraph refLn libEnv
--     refNode = dgn_node nodelab
--     inEdgesInRefGraph = [(refLn,inEdge)| inEdge <- innDG refGraph refNode]

-------------------------------------------
-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
-- changed
computeTheory :: Bool -> -- True for using normal forms
                 LibEnv -> LIB_NAME -> Node -> Result (LibEnv, G_theory)
computeTheory useNf libEnv ln n =
   let dg = lookupDGraph ln libEnv
       nodeLab = labDG dg n
       inEdges = filter (liftE $ liftOr isLocalDef isGlobalDef) $ innDG dg n
       localTh = dgn_theory nodeLab
   in if (isDGRef nodeLab)
      then let refLn = dgn_libname nodeLab
               refNode = dgn_node nodeLab in do
         (libEnv', refTh) <- computeTheory useNf libEnv refLn refNode
         -- have to add local sentences,
         -- mapped along dgn_sigma if the node has hiding
         if useNf && (hasIngoingHidingDef libEnv' refLn refNode) then do
           let dg' = lookupDGraph refLn libEnv'
               newLab = labDG dg' refNode
               Just phi = dgn_sigma newLab
           mapTh <- translateG_theory phi localTh
           joinTh <- joinG_sentences (theoremsToAxioms $ refTh) mapTh
           return (libEnv', joinTh)
          else do
           joinTh <- joinG_sentences (theoremsToAxioms $ refTh) localTh
           return (libEnv', joinTh)
      else
   if useNf && (hasIngoingHidingDef libEnv ln n) then do
    case dgn_nf nodeLab of
     Nothing -> do
                 let nf = computeTheoryNf ln libEnv n
                 case maybeResult nf of
                   Nothing -> computeTheory False libEnv ln n
                   _ -> nf
     Just n' -> if (n /= n') then do
                    let nf = computeTheoryNf ln libEnv n
                    case maybeResult nf of
                       Nothing -> computeTheory False libEnv ln n
                       _ -> nf
                else computeTheoryReg useNf ln libEnv inEdges localTh
   else computeTheoryReg useNf ln libEnv inEdges localTh

computeTheoryNf :: LIB_NAME -> LibEnv -> Node -> Result (LibEnv, G_theory)
computeTheoryNf ln libEnv n = do
  libEnv' <- convertToNf ln libEnv n
  let dg' = lookupDGraph ln libEnv'
      nodelab = labDG dg' n
      Just nfN = dgn_nf nodelab
  computeTheory True libEnv' ln nfN

computeTheoryReg :: Bool -> LIB_NAME -> LibEnv -> [LEdge DGLinkLab] ->
                    G_theory -> Result (LibEnv, G_theory)
computeTheoryReg useNf ln libEnv inEdges localTh= do
     let dgraph = lookupDGraph ln libEnv
         (pathEdges, localEdges) = partition
           (\(sn, tn, _) -> (dgn_nf $ labDG dgraph sn) /= Just tn) inEdges
     (libEnv',ths) <- foldM (\ (x,l) e -> do
                            (x', t) <- computePathTheory useNf x ln e
                            return (x', t:l)) (libEnv, [])$
            sortBy (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1)
            $ pathEdges
     ths' <- mapM (\(sn, _tn, llab)->do
               let
                  phi = dgl_morphism llab
                  snlab = labDG dgraph sn
                  gth = dgn_theory snlab
               gth' <- translateG_theory phi gth
               return gth'
                ) localEdges
     gTh <- flatG_sentences localTh $ (reverse ths) ++ ths'
     return (libEnv', gTh)

computePathTheory :: Bool -> LibEnv -> LIB_NAME -> LEdge DGLinkLab ->
                     Result (LibEnv, G_theory)
computePathTheory useNf libEnv ln e@(src, _, link) = do
  (libEnv', th) <- if liftE isLocalDef e then do
           gth <- computeLocalTheory libEnv ln src
           return (libEnv, gth)
          else computeTheory useNf libEnv ln src
  -- translate theory and turn all imported theorems into axioms
  th' <- translateG_theory (dgl_morphism link) $ theoremsToAxioms th
  return (libEnv', th')

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
  G_theory lid sign ind1 (markAsAxiom True sens) ind2

