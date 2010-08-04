{- |
Module      :  $Header$
Description :  theorem hide shift proof rule for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
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
    ) where

import Logic.Logic

import Static.DevGraph
import Static.History

import Proofs.EdgeUtils
import Proofs.SimpleTheoremHideShift
  (thmHideShift, getInComingGlobalUnprovenEdges)

import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.Maybe

------------------------------------------------
-- Theorem hide shift and  auxiliaries
-----------------------------------------------

theoremHideShift :: LibName -> LibEnv -> Result LibEnv
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
  let newEdge =(sn, nfNode, defDGLink cmor globalThm DGLinkProof)
  case tryToGetEdge newEdge dg of
        Nothing -> let
          newGraph = changeDGH dg $ InsertEdge newEdge
          finalEdge = case getLastChange newGraph of
            InsertEdge final_e -> final_e
            _ -> error "Proofs.Global.globDecompForOneEdgeAux"
          in return
              (newGraph, addEdgeId emptyProofBasis $ getEdgeId finalEdge)
        Just e -> return (dg, addEdgeId emptyProofBasis $ getEdgeId e)

theoremHideShiftFromList :: LibName -> [LNode DGNodeLab] -> LibEnv
                         -> Result LibEnv
theoremHideShiftFromList ln ls =
  return . Map.adjust (theoremHideShiftAux ls) ln
