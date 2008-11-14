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
    , convertNodesToNf
    , hasIngoingHidingDef
    , computeTheory
    , theoremsToAxioms
    ) where

import Logic.Logic
import Logic.Prover

import Static.GTheory
import Static.DevGraph
import Static.WACocone

import Proofs.EdgeUtils
import Proofs.ComputeColimit
import Proofs.SimpleTheoremHideShift(getInComingGlobalUnprovenEdges)

import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.List (nub, sortBy)
import Control.Monad

convertNodesToNf :: LIB_NAME -> LibEnv -> Result LibEnv
convertNodesToNf ln libEnv = do
  libEnv' <- foldM (convertToNf ln) libEnv $
                  nodesDG $ lookupDGraph ln libEnv
  let oldGraph = lookupDGraph ln libEnv
      newGraph = lookupDGraph ln libEnv'
  return $ Map.insert ln
    (groupHistory oldGraph (DGRule "TheoremHideShift") newGraph) libEnv'

{- | converts the given node to its own normal form -}
convertToNf :: LIB_NAME -> LibEnv -> Node -> Result LibEnv
convertToNf ln libEnv node = do
 let dgraph = lookupDGraph ln libEnv
     nodelab = labDG dgraph node
 case dgn_nf nodelab of
  -- here checks if it's already been computed
  Just _ -> return libEnv
  Nothing ->
   case hasIngoingHidingDef libEnv ln node of
    False -> -- no hiding, nf is the node itself
             -- we need to update the fields
             -- dgn_sign and dgn_nf of node
             do
      let (sign, mor) = (dgn_theory nodelab, Just $ ide $ dgn_sign nodelab)
          newLab = (newNodeLab (dgn_name nodelab) DGProof sign){
                    dgn_nf = Just node,
                    dgn_sigma = mor}
          chLab = SetNodeLab nodelab (node, newLab)
          newGraph  = changeDGH dgraph chLab
      return $ Map.insert ln
        (groupHistory dgraph (DGRule "NormalForm") newGraph) libEnv
    True -> case isDGRef nodelab of
      True -> do
        -- the normal form of the node
        -- is a reference to the normal form of the node it references
        -- careful: here not refNf, but a new Node which references refN
       let refLib = dgn_libname nodelab
           refNode = dgn_node nodelab
       libEnv' <- convertToNf refLib libEnv refNode
       let
         refGraph' = lookupDGraph refLib libEnv'
         Just refNf = dgn_nf $ labDG refGraph' refNode
              -- the normal form just computed ^
         refNodelab = labDG refGraph' refNf
              -- the label of the normal form ^
         nfNode = getNewNodeDG dgraph
              -- the new reference node in the old graph ^
         NodeName tt _ss _ii = dgn_name nodelab
         nfName = mkSimpleId $ "NormalForm" ++ show tt ++ show node
         refLab = DGNodeLab{
                    dgn_name = NodeName nfName (show nfName) 0,
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
         changes = [InsertNode (nfNode, refLab), chLab]
         newGraph = changesDGH dgraph changes
       return $ Map.insert ln
         (groupHistory dgraph (DGRule "NormalForm") newGraph) libEnv'
      False -> do
          auxProofstatus <- createNfsForPredecessors ln libEnv node
          (diagram, g) <- computeDiagram ln auxProofstatus node
          let Result _ds res = gWeaklyAmalgamableCocone diagram
          case res of
              Nothing -> fail "convert to normal form: can't compute cocone"
              Just (sign, mmap) -> do
               let
            -- the new node which will contain the normal form
                auxGraph = lookupDGraph ln auxProofstatus
                nfNode = getNewNodeDG auxGraph
            -- the label of the new node
                NodeName tt ss _ii = dgn_name nodelab
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
                insStrMor = map (\ (x, f) -> InsertEdge $ makeEdge x nfNode f)
                  $ nub $ map (\ (x, y) -> (g Map.! x, y))
                  $ Map.toList mmap
                allChanges = chLab : insNNF : insStrMor
                newGraph = changesDGH auxGraph allChanges
               return $ Map.insert ln
                 (groupHistory auxGraph (DGRule "NormalForm") newGraph)
                 auxProofstatus

{- computes the diagram associated to a node N in a development graph,
   adding common origins for multiple occurences of nodes, whenever
   needed
-}
computeDiagram :: LIB_NAME -> LibEnv -> Node ->
                   Result (GDiagram, Map.Map Node Node) -- (D,G)
computeDiagram ln libEnv node =
  unfoldedGraph ln libEnv node
  -- as described in the paper for now

unfoldedGraph :: LIB_NAME -> LibEnv -> Node ->
                 Result (GDiagram, Map.Map Node Node)
unfoldedGraph ln libEnv node = do
 let dgraph = lookupDGraph ln libEnv
     gd = insNode (node, dgn_theory $ labDG dgraph node) empty
     g = Map.fromList [(node,node)]
 unfoldedGraphAux ln libEnv [node] node (gd, g)

unfoldedGraphAux :: LIB_NAME -> LibEnv -> [Node] -> Node ->
                    (GDiagram, Map.Map Node Node) ->
                    Result (GDiagram, Map.Map Node Node)
unfoldedGraphAux ln libEnv nodeList node (gd,g) =
 case nodeList of
  [] -> return (gd,g)
  _ -> do
   let dgraph = lookupDGraph ln libEnv
       -- defInEdges is list of pairs (n, edges of target g(n))
       defInEdges = map (\n -> (n,filter (\e@(s,t,_) -> s /= t &&
                         liftE (liftOr isGlobalDef isHidingDef) e) $
                        innDG dgraph $ g Map.! n))  nodeList
       -- TO DO: no local links, and why edges with s=t are removed
       --        add normal form nodes
       -- sources of each edge must be added as new nodes
       nodeIds = zip (newNodes (length $ concat $ map snd defInEdges) gd)
                     $ concatMap (\(n,l) -> map (\x -> (n,x)) l ) defInEdges
       newLNodes = zip (map fst nodeIds) $
                   map (\ (s,_,_) -> dgn_theory $ labDG dgraph s) $
                   concat $  map snd defInEdges
       g0 = Map.fromList $
                     map (\ (newS, (_newT, (s,_t, _))) -> (newS,s)) nodeIds
       morphEdge (n1,(n2, (_, _, el))) =
         if isHidingDef $ dgl_type el
            then (n2,n1,(x, dgl_morphism el))
            else (n1,n2,(x, dgl_morphism el))
         where EdgeId x = dgl_id el
       newLEdges = map morphEdge nodeIds
       gd' = insEdges newLEdges $ insNodes newLNodes gd
       g' = Map.union g g0
   unfoldedGraphAux ln libEnv (map fst nodeIds)  node (gd', g')

{- | creates the normal forms of the predecessors of the given node
 -}
createNfsForPredecessors :: LIB_NAME -> LibEnv -> Node -> Result LibEnv
createNfsForPredecessors ln proofstatus node =
  foldM (convertToNf ln) proofstatus predecessors
  where
    dgraph = lookupDGraph ln proofstatus
    defInEdges =  filter ( \e@(s,_,_) ->
                           liftE (liftOr isGlobalDef isHidingDef) e
                           && node /= s) $ innDG dgraph node
    predecessors = map (\ (src,_,_) -> src) defInEdges

{- | returns True, if the given node has at least one directly or
   indirectly (ie via an ingoing path of GlobalDef edges)
   ingoing HidingDef edge. returns False otherwise
 -}
hasIngoingHidingDef :: LibEnv -> LIB_NAME -> Node -> Bool
hasIngoingHidingDef libEnv ln node =
 let dgraph = lookupDGraph ln libEnv
     nodelab = labDG dgraph node
     ingoingEdges = innDG dgraph node
     hidingDefEdges = filter (liftE isHidingDef ) ingoingEdges
     globalDefEdges = filter (liftE isGlobalDef) ingoingEdges
     next = map (\ (s, _, _) ->  s) globalDefEdges
 in
 if isDGRef nodelab then
   -- if the referenced node has incoming hiding links
   -- then the reference is also treated as with hiding
   let DGRef refLib refNode = nodeInfo nodelab
   in hasIngoingHidingDef libEnv refLib refNode
 else
  not (null hidingDefEdges)
   || or (map (hasIngoingHidingDef libEnv ln) next)

------------------------------------------------
-- Theorem hide shift and  auxiliaries
-----------------------------------------------

theoremHideShift :: LIB_NAME -> LibEnv -> Result LibEnv
theoremHideShift ln proofStatus =
 theoremHideShiftAux ln proofStatus $ nodesDG $ lookupDGraph ln proofStatus

theoremHideShiftAux :: LIB_NAME -> LibEnv -> [Node] -> Result LibEnv
theoremHideShiftAux ln proofStatus nodeList = do
  auxProofstatus <- foldM (convertToNf ln) proofStatus $
                     nodesDG $ lookupDGraph ln proofStatus
  let
     auxGraph = lookupDGraph ln auxProofstatus

     nodesWHiding = filter (hasIngoingHidingDef proofStatus ln) nodeList
     -- all nodes with incoming hiding links
     -- all the theorem links entering these nodes
     -- have to replaced by theorem links with the same origin
     -- but pointing to the normal form of the former target node
     ingoingEdges = concat $
                    map (getInComingGlobalUnprovenEdges auxGraph) nodesWHiding
     newGraph = foldl theoremHideShiftForEdge auxGraph ingoingEdges
  return $ Map.insert ln
    (groupHistory auxGraph (DGRule "TheoremHideShift") newGraph)
         auxProofstatus

theoremHideShiftForEdge :: DGraph -> LEdge DGLinkLab -> DGraph
theoremHideShiftForEdge dg edge@(source, target, edgeLab) =
  case maybeResult $ theoremHideShiftForEdgeAux dg edge of
   Nothing -> error "theoremHideShiftForEdgeAux"
   Just (dg', pbasis) -> let
    GlobalThm _ conservativity conservStatus = dgl_type edgeLab
    provenEdge = (source, target, edgeLab
        { dgl_type = GlobalThm (Proven (DGRule "TheoremHideShift") pbasis)
            conservativity conservStatus
        , dgl_origin = DGLinkProof })
    in changesDGH dg' [DeleteEdge edge, InsertEdge provenEdge]

theoremHideShiftForEdgeAux :: DGraph -> LEdge DGLinkLab
                           -> Result (DGraph, ProofBasis)
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
          newGraph = changeDGH dg $ InsertEdge newEdge
          finalEdge = case getLastChange newGraph of
            InsertEdge final_e -> final_e
            _ -> error "Proofs.Global.globDecompForOneEdgeAux"
          in return
              (newGraph, addEdgeId emptyProofBasis $ getEdgeId finalEdge)
        Just e -> return (dg, addEdgeId emptyProofBasis $ getEdgeId e)

theoremHideShiftFromList :: LIB_NAME -> [LNode DGNodeLab] -> LibEnv
                         -> Result LibEnv
theoremHideShiftFromList ln ls proofStatus =
  theoremHideShiftAux ln proofStatus $ map fst ls

----------------------------------------------------
{- compute the theory of a node, using normal forms when available -}

computeTheory :: Bool -> LibEnv -> LIB_NAME -> Node ->
                 Result (LibEnv, G_theory)
computeTheory useNf libEnv ln n =
  let dg = lookupDGraph ln libEnv
      nodelab = labDG dg n
      inEdges = filter (liftE $ liftOr isLocalDef isGlobalDef) $ innDG dg n
      localTh = dgn_theory nodelab
  in
   if isDGRef nodelab then do
    let refLn = dgn_libname nodelab
        refNode = dgn_node nodelab
    (libEnv', refTh) <- computeTheory useNf libEnv refLn refNode
    -- local sentences have to be mapped along dgn_sigma if refNode has hiding
    localTh' <- if useNf && hasIngoingHidingDef libEnv' refLn refNode then
                  let dg' = lookupDGraph refLn libEnv'
                      newLab = labDG dg' refNode
                  in case dgn_sigma newLab of
                       Nothing -> return localTh
                        -- normal form computation failed
                       Just phi ->  translateG_theory phi localTh
                 else return localTh
    joinTh <- joinG_sentences (theoremsToAxioms refTh) localTh'
    return (libEnv', joinTh)
   else
    if useNf && hasIngoingHidingDef libEnv ln n then do
      let libEnvRes = convertToNf ln libEnv n
      case maybeResult libEnvRes of
       Nothing -> computeTheory False libEnv ln n
        -- if it fails or colimits are not implemented,
        -- use old version
       Just libEnv' -> do
         let dg' = lookupDGraph ln libEnv'
             nodelab' = labDG dg' n
             Just nfN = dgn_nf nodelab'
         computeTheory False libEnv' ln nfN
          -- set flag to False, so compute without checking hiding
          -- for normal form node
    else do
     ths <- mapM (computePathTheory libEnv ln) $ sortBy
            (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1) inEdges
     ths' <- flatG_sentences localTh ths
     return (libEnv, ths')

computePathTheory :: LibEnv -> LIB_NAME -> LEdge DGLinkLab -> Result G_theory
computePathTheory libEnv ln e@(src, _, link) = do
  th <- if liftE isLocalDef e then computeLocalTheory libEnv ln src
        else do
          (_, th') <- computeTheory False libEnv ln src
                      -- because this function is called only when flag is False
          return th'
  -- translate theory and turn all imported theorems into axioms
  translateG_theory (dgl_morphism link) $ theoremsToAxioms th

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2
