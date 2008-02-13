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


{- | applies global decomposition to the list of edges given (global
     theorem edges) if possible, if empty list is given then to all
     unproven global theorems.
     Notice: (for ticket 5, which solves the problem across library border)
     1. before the actual global decomposition is applied, the whole DGraph is
     updated firstly by calling the function updateDGraph.
     2. The changes of the update action should be added as the head of the
     history.
-}
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

{- | update the given DGraph with source nodes of all global unproven
     links.
     The idea is, to expand the given DGraph by adding all the referenced
     nodes related to the given source nodes in other libraries and the
     corresponding links as well.
     If a certain node is a referenced node and not expanded yet, then its
     prents will be found by calling getRefParents.
     These parents will be added into current DGraph using updateDGraphAux
-}
updateDGraph :: DGraph -> LibEnv -> [DGChange]
             -> [Node] -- source nodes of all global unproven links
             -> (DGraph, [DGChange])
updateDGraph dg _ changes [] = (dg, changes)
updateDGraph dg le changes (x:xs) =
    {- checks if it is an unexpanded referenced node
       the function lookupInRefNodesDG only checks the
       nodes which are not expanded. -}
    case lookupInRefNodesDG x dg of
         Just (refl, refn) ->
            let
            parents = getRefParents le refl refn
            {- important for those, who's doing redo/undo function:
               notice that if the node is expanded, then it should be
               deleted out of the unexpanded map using
               deleteFromRefNodesDG -}
            (auxDG, auxChanges) = updateDGraphAux le
                (deleteFromRefNodesDG x dg) changes x refl parents
            in
            updateDGraph auxDG le auxChanges xs
         _ -> updateDGraph dg le changes xs

{- | get all the parents, namely the related referenced nodes and the links
     between them and the present to be expanded node.
-}
getRefParents :: LibEnv -> LIB_NAME
              -> Node -- the present to be expanded node
              -> [(LNode DGNodeLab, [DGLinkLab])]
getRefParents le refl refn =
   let
   {- get the previous objects to the current one, which can be done using
      lpre too, but to make it more tracable, safeContextDG is used.
   -}
   dg = lookupDGraph refl le
   (pres, _, _ , _) = safeContextDG "Proofs.Global.getRefParents" dg refn
   in modifyPs dg pres

{- | modify the parents to a better form.
     e.g. if the list is like:
     [(a, 1), (b, 1), (c, 2), (d, 2), (e, 2)]
     which means that node 1 is related via links a and b, and node 2 is
     related via links c, d and e.
     then to advoid too many checking by inserting, we can modify the list
     above to a form like this:
     [(1, [a, b]), (2, [c, d, e])]
     which simplifies the inserting afterwards ;)
-}
modifyPs :: DGraph -> [(DGLinkLab, Node)] -> [(LNode DGNodeLab, [DGLinkLab])]
modifyPs dg ls =
   map
   (\(n, x) -> ((n, labDG dg n), x))
   $ modifyPsAux ls
   where
   modifyPsAux :: Ord a => [(b, a)] -> [(a, [b])]
   modifyPsAux l =
        Map.toList $ Map.fromListWith (++) [(k, [v])|(v, k)<-l]

{- | the actual update function to insert a list of related parents to the
     present to be expanded node.
     It inserts the related referenced node firstly by calling addParentNode.
     Then it inserts the related links by calling addParentLinks
     Notice that nodes have to be added firstly, so that the links can be
     connected to the inserted nodes ;), especially by adding to the change
     list.
-}
updateDGraphAux :: LibEnv -> DGraph -> [DGChange]
                -> Node -- the present to be expanded node
                -> LIB_NAME
                -> [(LNode DGNodeLab, [DGLinkLab])] -> (DGraph, [DGChange])
updateDGraphAux _ dg changes _ _ [] = (dg, changes)
updateDGraphAux libenv dg changes n refl ((pnl, pls):xs) =
   let
   ((auxDG, auxChanges), newN) = addParentNode libenv dg changes refl pnl
   (finalDG, finalChanges) = addParentLinks auxDG [] newN n pls
   in
   updateDGraphAux libenv finalDG (auxChanges++finalChanges) n refl xs

{- | add the given parent node into the current dgraph
-}
addParentNode :: LibEnv -> DGraph -> [DGChange] ->  LIB_NAME
              -> LNode DGNodeLab -- the referenced parent node
              -> ((DGraph, [DGChange]), Node)
addParentNode libenv dg changes refl (refn, oldNodelab) =
   let
   {-
     To advoid the chain which is desribed in ticket 5, the parent node should
     be a non referenced node firstly, so that the actual parent node can be
     related.
   -}
   (nodelab, newRefl, newRefn) = if isDGRef oldNodelab then
                let
                tempRefl = dgn_libname oldNodelab
                tempRefn = dgn_node oldNodelab
                originDG = lookupDGraph tempRefl libenv
                in
                (labDG originDG tempRefn, tempRefl, tempRefn)
             else (oldNodelab, refl, refn)
   {-
     Set the sgMap and tMap too.
     Notice for those who are doing undo/redo, because the DGraph is actually
     changed if the maps are changed ;)
   -}
   (sgMap, s) = sigMapI dg
   (tMap, t) = thMapI dg
   -- creates an empty GTh, please check the definition of this function
   -- because there can be some problem or errors at this place.
   newGTh = createGThWith (dgn_theory nodelab) (s+1) (t+1)
   newRefNode = newInfoNodeLab (dgn_name nodelab)
     (newRefInfo newRefl newRefn) newGTh

   in
   -- checks if this node exists in the current dg, if so, nothing needs to be
   -- done.
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

{- | add a list of links between the given two node ids.
-}
addParentLinks :: DGraph -> [DGChange] -> Node -> Node -> [DGLinkLab]
                  -> (DGraph, [DGChange])
addParentLinks dg changes src tgt ls = updateWithChanges
 [ InsertEdge (src, tgt, x { dgl_id = defaultEdgeId
                           , dgl_type = invalidateProof $ dgl_type x })
   | x <- ls] dg changes

{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp ::LIB_NAME -> LibEnv -> LibEnv
globDecomp ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        globalThmEdges = labEdgesDG dgraph
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
  globDecompForOneEdgeAux dgraph edge [] paths emptyProofBasis
  where
    defEdgesToSource = [e | e@(_, _, lbl) <- innDG dgraph source,
                        isDefEdge (dgl_type lbl)]
    paths = map (\e -> [e,edge]) defEdgesToSource ++ [[edge]]
            -- why not? [edge] : map ...

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange]
                        -> [[LEdge DGLinkLab]] -> ProofBasis
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
globDecompForOneEdgeAux dgraph edge@(_,target,_) changes (path : list)
  proof_basis =
  case tryToGetEdge newEdge dgraph changes of
       Nothing -> globDecompForOneEdgeAux newGraph edge newChanges list
                  $ addEdgeId proof_basis $ getEdgeId finalEdge
       Just e -> globDecompForOneEdgeAux dgraph edge changes list
                  $ addEdgeId proof_basis $ getEdgeId e
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
                dgl_id = defaultEdgeId})
    globalEdge = (node,
                  target,
                  DGLink {dgl_morphism = morphism,
                          dgl_type = (GlobalThm LeftOpen
                                      None LeftOpen),
                          dgl_origin = DGProof,
                          dgl_id = defaultEdgeId}
                 )
    localEdge = (node,
                 target,
                 DGLink {dgl_morphism = morphism,
                         dgl_type = (LocalThm LeftOpen
                                     None LeftOpen),
                         dgl_origin = DGProof,
                         dgl_id = defaultEdgeId}
               )
    (newGraph, newChanges) = updateWithOneChange (InsertEdge newEdge)
                                                 dgraph changes
    finalEdge = case head newChanges of
                     InsertEdge final_e -> final_e
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
        globalThmEdges = labEdgesDG dgraph
    in globSubsumeFromList ln globalThmEdges libEnv

{- auxiliary function for globSubsume (above) the actual implementation -}
globSubsumeAux :: LibEnv ->  DGraph -> ([DGRule],[DGChange])
               -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux _ dgraph historyElement [] = (dgraph, historyElement)
globSubsumeAux libEnv dgraph (rules,changes) (ledge@(src,tgt,edgeLab) : list) =
  if not (nullProofBasis proofbasis) || isIdentityEdge ledge libEnv dgraph
   then
     let
     (auxDGraph, auxChanges) =
          updateWithOneChange (DeleteEdge ledge) dgraph changes
     (newDGraph, newChanges) =
          updateWithOneChange (InsertEdge newEdge) auxDGraph auxChanges
     in
     globSubsumeAux libEnv newDGraph (newRules, newChanges) list
   else
     globSubsumeAux libEnv dgraph (rules,changes) list
  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllGlobPathsOfMorphismBetween dgraph morphism src tgt
    filteredPaths = filter (noPath ledge) allPaths
    proofbasis = selectProofBasis dgraph ledge filteredPaths
    (GlobalThm _ conservativity conservStatus) = dgl_type edgeLab
    newEdge = (src,
               tgt,
               DGLink {dgl_morphism = morphism,
                       dgl_type = (GlobalThm (Proven (GlobSubsumption ledge)
                                              proofbasis)
                                   conservativity conservStatus),
                       dgl_origin = DGProof,
                       dgl_id = dgl_id edgeLab}
               )
    newRules = GlobSubsumption ledge : rules
