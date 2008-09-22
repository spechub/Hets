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
import Data.List

import Static.GTheory
import Static.DevGraph
import Common.LibName

import Proofs.EdgeUtils
import Proofs.StatusUtils

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
        (auxGraph, auxChanges) = mapAccumL (updateDGraph proofStatus) dgraph
           $ map (\ (src, _, _) -> src) finalGlobalThmEdges
        (newDGraph, newHistoryElem) = mapAccumL
            globDecompAux auxGraph finalGlobalThmEdges
    in mkResultProofStatus ln proofStatus newDGraph
       (concatMap fst newHistoryElem,
        concat auxChanges ++ concatMap snd newHistoryElem)

{- | update the given DGraph with source nodes of all global unproven
     links.
     The idea is, to expand the given DGraph by adding all the referenced
     nodes related to the given source nodes in other libraries and the
     corresponding links as well.
     If a certain node is a referenced node and not expanded yet, then its
     parents will be found by calling getRefParents.
     These parents will be added into current DGraph using updateDGraphAux
-}
updateDGraph :: LibEnv -> DGraph
             -> Node -- source nodes of all global unproven links
             -> (DGraph, [DGChange])
updateDGraph le dg x =
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
            (auxDG, auxChanges) = mapAccumL (updateDGraphAux le x refl)
                (deleteFromRefNodesDG x dg) parents
            in (auxDG, concat auxChanges)
         _ -> (dg, [])

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
   (\ (n, x) -> ((n, labDG dg n), x))
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
updateDGraphAux :: LibEnv -> Node -- the present to be expanded node
                -> LIB_NAME -> DGraph -> (LNode DGNodeLab, [DGLinkLab])
                -> (DGraph, [DGChange])
updateDGraphAux libenv n refl dg (pnl, pls) =
   let
   ((auxDG, auxChanges), newN) = addParentNode libenv dg refl pnl
   (finalDG, finalChanges) = addParentLinks auxDG newN n pls
   in (finalDG, auxChanges ++ finalChanges)

{- | add the given parent node into the current dgraph
-}
addParentNode :: LibEnv -> DGraph ->  LIB_NAME
              -> LNode DGNodeLab -- the referenced parent node
              -> ((DGraph, [DGChange]), Node)
addParentNode libenv dg refl (refn, oldNodelab) =
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
   newGTh = createGThWith (dgn_theory nodelab) (succ s) (succ t)
   refInfo = newRefInfo newRefl newRefn
   newRefNode = newInfoNodeLab (dgn_name nodelab) refInfo newGTh

   in
   -- checks if this node exists in the current dg, if so, nothing needs to be
   -- done.
   case lookupInAllRefNodesDG refInfo dg of
        Nothing ->
           let
           newN = getNewNodeDG dg
           in
           (updateWithOneChange
           (InsertNode (newN, newRefNode))
           (setThMapDG (Map.insert (succ t) newGTh tMap)
           $ setSigMapDG (Map.insert (succ s) (signOf newGTh) sgMap)
           $ addToRefNodesDG newN refInfo dg), newN)
        Just extN -> ((dg, []), extN)

{- | add a list of links between the given two node ids.
-}
addParentLinks :: DGraph -> Node -> Node -> [DGLinkLab] -> (DGraph, [DGChange])
addParentLinks dg src tgt ls = updateWithChanges
 [ InsertEdge (src, tgt, x { dgl_id = defaultEdgeId
                           , dgl_type = invalidateProof $ dgl_type x })
   | x <- ls] dg

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
globDecompAux :: DGraph -> LEdge DGLinkLab -> (DGraph, ([DGRule], [DGChange]))
globDecompAux dgraph edge =
  let (newDGraph, newChanges) = globDecompForOneEdge dgraph edge
  in (newDGraph, ([GlobDecomp edge], newChanges))

-- applies global decomposition to a single edge
globDecompForOneEdge :: DGraph -> LEdge DGLinkLab -> (DGraph, [DGChange])
globDecompForOneEdge dgraph edge@(source, target, edgeLab) = let
    defEdgesToSource = [e | e@(_, _, lbl) <- innDG dgraph source,
                        isDefEdge (dgl_type lbl)]
    paths = map (\e -> [e, edge]) defEdgesToSource ++ [[edge]]
             -- why not? [edge] : map ...
    ((newGr,  proof_basis), changes) = mapAccumL
      (globDecompForOneEdgeAux target) (dgraph, emptyProofBasis) paths
    GlobalThm _ conservativity conservStatus = dgl_type edgeLab
    provenEdge = (source, target, edgeLab
        { dgl_type = GlobalThm (Proven (GlobDecomp edge) proof_basis)
            conservativity conservStatus
        , dgl_origin = DGLinkProof })
    (dg2, insC) = updateWithChanges [DeleteEdge edge, InsertEdge provenEdge]
                    newGr
    in (dg2, concat changes ++ insC)


{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: Node -> (DGraph, ProofBasis)
                        -> [LEdge DGLinkLab]
                        -> ((DGraph, ProofBasis), [DGChange])
-- for each path an unproven localThm edge is inserted
globDecompForOneEdgeAux target (dgraph, proof_basis) path =
  case path of
    [] -> error "globDecompForOneEdgeAux"
    (node, _, lbl) : rpath -> let
      lbltype = dgl_type lbl
      isHiding = isHidingDef lbltype
      morphismPath = if isHiding then rpath else path
      morphism = case calculateMorphismOfPath morphismPath of
        Just morph -> morph
        Nothing -> error "globDecomp: could not determine morphism of new edge"
      newEdge = (node, target, DGLink
        { dgl_morphism = morphism
        , dgl_type = if isHiding then
            HidingThm (dgl_morphism $ lbl) LeftOpen
            else (if isGlobalDef lbltype then
                      GlobalThm else LocalThm) LeftOpen None LeftOpen
        , dgl_origin = DGLinkProof
        , dgl_id = defaultEdgeId })
      in case tryToGetEdge newEdge dgraph of
        Nothing -> let
          (newGraph, newChange) =
            updateWithOneChange (InsertEdge newEdge) dgraph
          finalEdge = case newChange of
            [InsertEdge final_e] -> final_e
            _ -> error "Proofs.Global.globDecompForOneEdgeAux"
          in ((newGraph, addEdgeId proof_basis $ getEdgeId finalEdge)
             , newChange)
        Just e -> ((dgraph, addEdgeId proof_basis $ getEdgeId e), [])

globSubsumeFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globSubsumeFromList ln globalThmEdges libEnv =
    let dgraph = lookupDGraph ln libEnv
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        (nextDGraph, nextHistoryElems) = mapAccumL
            (globSubsumeAux libEnv) dgraph finalGlobalThmEdges
    in mkResultProofStatus ln libEnv nextDGraph
       (concatMap fst nextHistoryElems, concatMap snd nextHistoryElems)

-- | tries to apply global subsumption to all unproven global theorem edges
globSubsume :: LIB_NAME -> LibEnv -> LibEnv
globSubsume ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        globalThmEdges = labEdgesDG dgraph
    in globSubsumeFromList ln globalThmEdges libEnv

{- auxiliary function for globSubsume (above) the actual implementation -}
globSubsumeAux :: LibEnv ->  DGraph -> LEdge DGLinkLab
               -> (DGraph, ([DGRule], [DGChange]))
globSubsumeAux libEnv dgraph ledge@(src, tgt, edgeLab) =
  let morphism = dgl_morphism edgeLab
      filteredPaths = filterPathsByMorphism morphism $ filter (noPath ledge)
                    $ getAllGlobPathsBetween dgraph src tgt
      proofbasis = selectProofBasis dgraph ledge filteredPaths
  in if not (nullProofBasis proofbasis) || isIdentityEdge ledge libEnv dgraph
   then
     let GlobalThm _ conservativity conservStatus = dgl_type edgeLab
         newEdge = (src, tgt, edgeLab
               { dgl_type = GlobalThm
                   (Proven (GlobSubsumption ledge) proofbasis)
                   conservativity conservStatus
               , dgl_origin = DGLinkProof })
         (newDGraph, newChanges) = updateWithChanges
           [DeleteEdge ledge, InsertEdge newEdge] dgraph
     in (newDGraph, ([GlobSubsumption ledge], newChanges))
   else (dgraph, emptyHistory)
