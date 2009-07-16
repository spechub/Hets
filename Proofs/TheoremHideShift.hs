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
    , computeTheory
    , computeLabelTheory
    , theoremsToAxioms
    ) where

import Logic.Logic
import Logic.Prover

import Static.GTheory
import Static.DevGraph

import Proofs.EdgeUtils
import Proofs.SimpleTheoremHideShift
  (thmHideShift, getInComingGlobalUnprovenEdges)

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.Maybe
import Data.List (sortBy)
import Control.Monad

------------------------------------------------
-- Theorem hide shift and  auxiliaries
-----------------------------------------------

theoremHideShift :: LIB_NAME -> LibEnv -> Result LibEnv
theoremHideShift ln = return .
  Map.adjust (\ dg -> theoremHideShiftAux (labNodesDG dg) dg) ln

-- | assume that the normal forms a commputed already.
-- return Nothing if nothing changed
theoremHideShiftAux :: [LNode DGNodeLab] -> DGraph -> DGraph
theoremHideShiftAux ns dg = let
  nodesWHiding = map fst $ filter
           (\ (_, lbl) -> labelHasHiding lbl && isJust (dgn_nf lbl)
           && isJust (dgn_sigma lbl)) ns
     -- all nodes with incoming hiding links
     -- all the theorem links entering these nodes
     -- have to replaced by theorem links with the same origin
     -- but pointing to the normal form of the former target node
  ingoingEdges = concatMap (getInComingGlobalUnprovenEdges dg) nodesWHiding
  in foldl theoremHideShiftForEdge dg ingoingEdges

theoremHideShiftForEdge :: DGraph -> LEdge DGLinkLab -> DGraph
theoremHideShiftForEdge dg edge@(source, target, edgeLab) =
  case maybeResult $ theoremHideShiftForEdgeAux dg edge of
   Nothing -> error "theoremHideShiftForEdgeAux"
   Just (dg', pbasis) -> let
    provenEdge = (source, target, edgeLab
        { dgl_type = setProof (Proven thmHideShift pbasis) $ dgl_type edgeLab
        , dgl_origin = DGLinkProof
        , dgl_id = defaultEdgeId })
    in insertDGLEdge provenEdge $ changeDGH dg' $ DeleteEdge edge

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
                 dgl_type = globalThm,
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
theoremHideShiftFromList ln ls =
  return . Map.adjust (theoremHideShiftAux ls) ln

-- | compute the theory of a node, using normal forms when available
computeLabelTheory :: LibEnv -> DGraph -> LNode DGNodeLab -> Result G_theory
computeLabelTheory libEnv dg (n, nodelab) =
  let localTh = dgn_theory nodelab in
  if isDGRef nodelab then do
    let refNode = dgn_node nodelab
        dg' = lookupDGraph (dgn_libname nodelab) libEnv
        newLab = labDG dg' refNode
    refTh <- computeLabelTheory libEnv dg' (refNode, newLab)
    joinG_sentences (theoremsToAxioms refTh) localTh
  else do
    ths <- mapM (computePathTheory libEnv dg) $ sortBy
            (\ (_, _, l1) (_, _, l2) -> compare (dgl_id l2) $ dgl_id l1)
            $ filter (liftE (\ l -> isDefEdge l && not (isHidingEdge l)))
            $ innDG dg n
    flatG_sentences localTh ths

computeNodeTheory :: LibEnv -> DGraph -> Node -> Result G_theory
computeNodeTheory libEnv dg n = computeLabelTheory libEnv dg (n, labDG dg n)

computeTheory :: LibEnv -> LIB_NAME -> Node -> Result G_theory
computeTheory libEnv ln = computeNodeTheory libEnv $ lookupDGraph ln libEnv

computePathTheory :: LibEnv -> DGraph -> LEdge DGLinkLab -> Result G_theory
computePathTheory libEnv dg e@(src, _, link) = do
  th <- if liftE isLocalDef e then computeLocalNodeTheory libEnv dg src
        else computeNodeTheory libEnv dg src
  -- translate theory and turn all imported theorems into axioms
  translateG_theory (dgl_morphism link) $ theoremsToAxioms th

theoremsToAxioms :: G_theory -> G_theory
theoremsToAxioms (G_theory lid sign ind1 sens ind2) =
     G_theory lid sign ind1 (markAsAxiom True sens) ind2
