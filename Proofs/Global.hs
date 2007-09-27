{- |
Module      :  $Header$
Description :  global proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

global proof rules for development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

module Proofs.Global
    ( globSubsume
    , globDecomp
    , globDecompAux -- for Test.hs
    , globDecompFromList
    , globSubsumeFromList
    ) where

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map

import Static.GTheory
import Static.DevGraph
import Static.DGToSpec
import Syntax.AS_Library

import Proofs.EdgeUtils
import Proofs.StatusUtils

-- ---------------------
-- global decomposition
-- ---------------------

{- apply rule GlobDecomp to all global theorem links in the current DG
   current DG = DGm
   add to proof status the pair ([GlobDecomp e1,...,GlobDecomp en],DGm+1)
   where e1...en are the global theorem links in DGm
   DGm+1 results from DGm by application of GlobDecomp e1,...,GlobDecomp en -}


{- applies global decomposition to the list of edges given (global
   theorem edges) if possible, if empty list is given then to all
   unproven global theorems -}
globDecompFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globDecompFromList ln globalThmEdges proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        (auxGraph, auxChanges) = updateDGraph dgraph proofStatus []
                                 $ map getLEdgeSrc finalGlobalThmEdges
        (newDGraph, newHistoryElem) =
            globDecompAux auxGraph finalGlobalThmEdges ([], [])
    in mkResultProofStatus ln proofStatus newDGraph
       (fst newHistoryElem, auxChanges ++ snd newHistoryElem)

updateDGraph :: DGraph -> LibEnv -> [DGChange] -> [Node]
             -> (DGraph, [DGChange])
updateDGraph dg _ changes [] = (dg, changes)
updateDGraph dg le changes (x:xs) =
    case lookupInRefNodesDG x dg of
         Just (refl, refn) ->
            let
            parents = getRefParents le refl refn
            -- to be continued with undo...
            (auxDG, auxChanges) = updateDGraphAux le
                (deleteFromRefNodesDG x dg) changes x refl parents
            in
            updateDGraph auxDG le auxChanges xs
         _ -> updateDGraph dg le changes xs

getRefParents :: LibEnv -> LIB_NAME -> Node -> [(LNode DGNodeLab, [DGLinkLab])]
getRefParents le refl refn =
   let
   dg = lookupDGraph refl le
   (pres, _, _ , _) = safeContextDG "Proofs.Global.getRefParents" dg refn
   in modifyPs dg pres

modifyPs :: DGraph -> [(DGLinkLab, Node)] -> [(LNode DGNodeLab, [DGLinkLab])]
modifyPs dg ls =
   map
   (\(n, x) -> ((n, lab' $ safeContextDG "Proofs.Global.modifyPs" dg n), x))
   $ modifyPsAux ls
   where
   modifyPsAux :: Ord a => [(b, a)] -> [(a, [b])]
   modifyPsAux l =
        Map.toList $ Map.fromListWith (++) [(k, [v])|(v, k)<-l]

updateDGraphAux :: LibEnv -> DGraph -> [DGChange] -> Node -> LIB_NAME
                -> [(LNode DGNodeLab, [DGLinkLab])] -> (DGraph, [DGChange])
updateDGraphAux _ dg changes _ _ [] = (dg, changes)
updateDGraphAux libenv dg changes n refl ((pnl, pls):xs) =
   let
   ((auxDG, auxChanges), newN) = addParentNode libenv dg changes refl pnl
   (finalDG, finalChanges) = addParentLinks auxDG [] newN n pls
   in
   updateDGraphAux libenv finalDG (auxChanges++finalChanges) n refl xs

addParentNode :: LibEnv -> DGraph -> [DGChange] ->  LIB_NAME
              -> LNode DGNodeLab -> ((DGraph, [DGChange]), Node)
addParentNode libenv dg changes refl (refn, oldNodelab) =
   let
   -- to be modified due to undo function...
   (nodelab, newRefl, newRefn) = if isDGRef oldNodelab then
                let
                tempRefl = dgn_libname oldNodelab
                tempRefn = dgn_node oldNodelab
                originDG = lookupDGraph tempRefl libenv
                in
                (lab' $ safeContextDG "Proofs.Global.addParentNode"
                                     originDG tempRefn,
                tempRefl, tempRefn)
             else (oldNodelab, refl, refn)
   (sgMap, s) = sigMapI dg
   (tMap, t) = thMapI dg
   newGTh = createGThWith (dgn_theory nodelab) (s+1) (t+1)
   newRefNode =
     DGRef{ dgn_name = dgn_name nodelab
          , dgn_libname = newRefl
          , dgn_node = newRefn
          , dgn_theory = newGTh
          , dgn_nf = Nothing
          , dgn_sigma = Nothing
          , dgn_lock = error "uninitialized MVar of DGRef"
          }
   in
   case (lookupInAllRefNodesDG (newRefl, newRefn) dg) of
        Nothing ->
           let
           newN = getNewNodeDG dg
           in
           (updateWithOneChange
           (InsertNode (newN, newRefNode))
           (setThMapDG (Map.insert (t+1) newGTh tMap)
           $ setSigMapDG (Map.insert (s+1) (signOf newGTh) sgMap)
           $ addToRefNodesDG (newN, newRefl, newRefn) dg)
           changes, newN)
        Just extN -> ((dg, changes), extN)

addParentLinks :: DGraph -> [DGChange] -> Node -> Node -> [DGLinkLab]
                  -> (DGraph, [DGChange])
addParentLinks dg changes src tgt ls =
   updateWithChanges [InsertEdge (src, tgt, x)|x<-ls] dg changes

{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp ::LIB_NAME -> LibEnv -> LibEnv
globDecomp ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        globalThmEdges = filter (liftE isUnprovenGlobalThm) $ labEdgesDG dgraph
    in -- trace (show $ refNodes dgraph)
    globDecompFromList ln globalThmEdges proofStatus

{- auxiliary function for globDecomp (above)
   actual implementation -}
globDecompAux :: DGraph -> [LEdge DGLinkLab] -> ([DGRule],[DGChange])
              -> (DGraph,([DGRule],[DGChange]))
globDecompAux dgraph [] historyElem = (dgraph, historyElem)
globDecompAux dgraph (edge:list) historyElem =
  globDecompAux newDGraph list newHistoryElem
  where
    (newDGraph, newChanges) = globDecompForOneEdge dgraph edge
    newHistoryElem = (((GlobDecomp edge):(fst historyElem)),
                        (newChanges++(snd historyElem)))

-- applies global decomposition to a single edge
globDecompForOneEdge :: DGraph -> LEdge DGLinkLab -> (DGraph,[DGChange])
globDecompForOneEdge dgraph edge@(source, _, _) =
  globDecompForOneEdgeAux dgraph edge [] paths []
  where
    defEdgesToSource = [e | e@(_, tgt, lbl) <- labEdgesDG dgraph,
                        isDefEdge (dgl_type lbl) && tgt == source]
    paths = map (\e -> [e,edge]) defEdgesToSource ++ [[edge]]

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange]
                        -> [[LEdge DGLinkLab]] -> [EdgeID]
                        -> (DGraph,[DGChange])
{- if the list of paths is empty from the beginning, nothing is done
   otherwise the unprovenThm edge is replaced by a proven one -}
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes
                        [] proof_basis =
  insertDGLEdge provenEdge auxDGraph auxChanges
  where
    (GlobalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    provenEdge = (source,
                  target,
                  DGLink {dgl_morphism = dgl_morphism edgeLab,
                          dgl_type =
                            (GlobalThm (Proven (GlobDecomp edge) proof_basis)
                             conservativity conservStatus),
                          dgl_origin = DGProof,
                          dgl_id = dgl_id edgeLab}
                  )
    (auxDGraph, auxChanges) =
        updateWithOneChange (DeleteEdge edge) dgraph changes

-- for each path an unproven localThm edge is inserted
globDecompForOneEdgeAux dgraph edge@(_,target,_) changes
 (path:list)  proof_basis =
  case (tryToGetEdge newEdge dgraph changes) of
       Nothing -> globDecompForOneEdgeAux newGraph edge newChanges list
                                         (getEdgeID finalEdge:proof_basis)
       Just e -> globDecompForOneEdgeAux dgraph edge changes list
                                         (getEdgeID e:proof_basis)
{-
  if isDuplicate newEdge dgraph changes-- list
    then globDecompForOneEdgeAux dgraph edge changes list
   else globDecompForOneEdgeAux newGraph edge newChanges list
-}
  where
    (node, _, lbl) = head path
    lbltype = dgl_type lbl
    isHiding = not (null path) && isHidingDef lbltype
    morphismPath = if isHiding then tail path else path
    morphism = case calculateMorphismOfPath morphismPath of
                 Just morph -> morph
                 Nothing ->
                   error "globDecomp: could not determine morphism of new edge"
    newEdge = if isHiding then hidingEdge
              else if isGlobalDef lbltype
                   then globalEdge
                   else localEdge
    hidingEdge =
       (node,
        target,
        DGLink {dgl_morphism = morphism,
                dgl_type = HidingThm (dgl_morphism $ lbl) LeftOpen,
                dgl_origin = DGProof,
                dgl_id = defaultEdgeID})
    globalEdge = (node,
                  target,
                  DGLink {dgl_morphism = morphism,
                          dgl_type = (GlobalThm LeftOpen
                                      None LeftOpen),
                          dgl_origin = DGProof,
                          dgl_id = defaultEdgeID}
                 )
    localEdge = (node,
                 target,
                 DGLink {dgl_morphism = morphism,
                         dgl_type = (LocalThm LeftOpen
                                     None LeftOpen),
                         dgl_origin = DGProof,
                         dgl_id = defaultEdgeID}
               )
    (newGraph, newChanges) = updateWithOneChange (InsertEdge newEdge)
                                                 dgraph changes
    finalEdge = case (head newChanges) of
                     (InsertEdge final_e) -> final_e
                     _ -> error "Proofs.Global.globDecompForOneEdgeAux"

-- -------------------
-- global subsumption
-- -------------------

globSubsumeFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globSubsumeFromList ln globalThmEdges libEnv =
    let dgraph = lookupDGraph ln libEnv
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        (nextDGraph, nextHistoryElem) =
            globSubsumeAux libEnv dgraph ([],[]) finalGlobalThmEdges
    in mkResultProofStatus ln libEnv nextDGraph nextHistoryElem

-- | tries to apply global subsumption to all unproven global theorem edges
globSubsume :: LIB_NAME -> LibEnv -> LibEnv
globSubsume ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        globalThmEdges = filter (liftE isUnprovenGlobalThm) $ labEdgesDG dgraph
    in globSubsumeFromList ln globalThmEdges libEnv

{- auxiliary function for globSubsume (above) the actual implementation -}
globSubsumeAux :: LibEnv ->  DGraph -> ([DGRule],[DGChange])
               -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux _ dgraph historyElement [] = (dgraph, historyElement)
globSubsumeAux libEnv dgraph (rules,changes) (ledge@(src,tgt,edgeLab) : list) =
  if not (null proofBasis) || isIdentityEdge ledge libEnv dgraph
   then
     let
     (auxDGraph, auxChanges) =
          updateWithOneChange (DeleteEdge ledge) dgraph changes
     (newDGraph, newChanges) =
          insertDGLEdge newEdge auxDGraph auxChanges
     in
     globSubsumeAux libEnv newDGraph (newRules, newChanges) list
   else
     globSubsumeAux libEnv dgraph (rules,changes) list
  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllGlobPathsOfMorphismBetween dgraph morphism src tgt
    filteredPaths = filter (notElem ledge) allPaths
    proofBasis = selectProofBasis dgraph ledge filteredPaths
    (GlobalThm _ conservativity conservStatus) = dgl_type edgeLab
    newEdge = (src,
               tgt,
               DGLink {dgl_morphism = morphism,
                       dgl_type = (GlobalThm (Proven (GlobSubsumption ledge)
                                              proofBasis)
                                   conservativity conservStatus),
                       dgl_origin = DGProof,
                       dgl_id = dgl_id edgeLab}
               )
    newRules = (GlobSubsumption ledge):rules

