{- |
Module      :  ./Proofs/Global.hs
Description :  global proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
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
import Data.Maybe

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.History

import Common.LibName
import Common.Utils

import Proofs.EdgeUtils
import Proofs.StatusUtils

globDecompRule :: EdgeId -> DGRule
globDecompRule = DGRuleWithEdge "Global-Decomposition"

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
globDecompFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globDecompFromList ln globalThmEdges proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        auxGraph = foldl (updateDGraph proofStatus) dgraph
           $ nubOrd $ map (\ (src, _, _) -> src) finalGlobalThmEdges
        newDGraph = foldl globDecompAux auxGraph finalGlobalThmEdges
    in Map.insert ln newDGraph proofStatus

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
             -> DGraph
updateDGraph le dg x =
    case lookupRefNodeM le Nothing dg x of
      (Just refl, refDg, (refn, _)) ->
            let
            parents = getRefParents refDg refn
            {- important for those, who's doing redo/undo function:
               notice that if the node is expanded, then it should be
               deleted out of the unexpanded map using
               deleteFromRefNodesDG -}
            auxDG = foldl (updateDGraphAux le x refl refDg)
                dg parents
            in auxDG
      _ -> dg

{- | get all the parents, namely the related referenced nodes and the links
     between them and the present to be expanded node.
-}
getRefParents :: DGraph
              -> Node -- the present to be expanded node
              -> [(Node, [DGLinkLab])]
getRefParents dg refn =
   let
   -- get the previous objects to the current one
   pres = innDG dg refn
   in modifyPs pres

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

modifyPs :: [LEdge DGLinkLab] -> [(Node, [DGLinkLab])]
modifyPs = Map.toList . Map.fromListWith (++)
  . map (\ (k, _, v) -> (k, [v]))

{- | the actual update function to insert a list of related parents to the
     present to be expanded node.
     It inserts the related referenced node first by calling addParentNode.
     Then it inserts the related links by calling addParentLinks.
-}
updateDGraphAux :: LibEnv -> Node -- the present to be expanded node
                -> LibName
                -> DGraph -- ^ the reference graph for the libname
                -> DGraph -> (Node, [DGLinkLab])
                -> DGraph
updateDGraphAux libenv n refl refDg dg (pn, pls) =
   let
   (auxDG, newN) = addParentNode libenv dg refl refDg pn
   in addParentLinks auxDG newN n pls

-- | add the given parent node into the current dgraph
addParentNode :: LibEnv -> DGraph -> LibName
              -> DGraph -- ^ the reference graph for the libname
              -> Node -- the referenced parent node
              -> (DGraph, Node)
addParentNode libenv dg refl refDg refn =
   let
   {-
     To advoid the chain which is desribed in ticket 5, the parent node should
     be a non referenced node firstly, so that the actual parent node can be
     related.
   -}
   (newRefl, _, (newRefn, nodelab)) = lookupRefNode libenv refl
     refDg refn
   {-
     Set the sgMap and tMap too.
     Notice for those who are doing undo/redo, because the DGraph is actually
     changed if the maps are changed ;)

   creates an empty GTh, please check the definition of this function
   because there can be some problem or errors at this place. -}
   newGTh = case dgn_theory nodelab of
     G_theory lid _ sig ind _ _ -> noSensGTheory lid sig ind
   refInfo = newRefInfo newRefl newRefn
   newRefNode = (newInfoNodeLab (dgn_name nodelab) refInfo newGTh)
     { globalTheory = globalTheory nodelab }
   in
   {- checks if this node exists in the current dg, if so, nothing needs to be
   done. -}
   case lookupInAllRefNodesDG refInfo dg of
        Nothing -> let newN = getNewNodeDG dg in
           (changeDGH dg $ InsertNode (newN, newRefNode), newN)
        Just extN -> (dg, extN)

-- | add a list of links between the given two node ids.
addParentLinks :: DGraph -> Node -> Node -> [DGLinkLab] -> DGraph
addParentLinks dg src tgt ls =
  let oldLinks = map (\ (_, _, l) -> l)
        $ filter (\ (s, _, _) -> s == src) $ innDG dg tgt
      newLinks = map (\ l -> l
                         { dgl_id = defaultEdgeId
                         , dgl_type = invalidateProof $ dgl_type l }) ls
  in if null oldLinks then
         changesDGH dg $ map (\ l -> InsertEdge (src, tgt, l)) newLinks
     else dg -- assume ingoing links are already properly set

{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp :: LibName -> LibEnv -> LibEnv
globDecomp ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        globalThmEdges = labEdgesDG dgraph
    in
    globDecompFromList ln globalThmEdges proofStatus

{- auxiliary function for globDecomp (above)
   actual implementation -}
globDecompAux :: DGraph -> LEdge DGLinkLab -> DGraph
globDecompAux dgraph edge =
  let newDGraph = globDecompForOneEdge dgraph edge
  in groupHistory dgraph (globDecompRule $ getEdgeId edge) newDGraph

-- applies global decomposition to a single edge
globDecompForOneEdge :: DGraph -> LEdge DGLinkLab -> DGraph
globDecompForOneEdge dgraph edge@(source, target, edgeLab) = let
    defEdgesToSource = filter (liftE isDefEdge) $ innDG dgraph source
    paths = [edge] : map (: [edge]) defEdgesToSource
    (newGr, proof_basis) = foldl
      (globDecompForOneEdgeAux target) (dgraph, emptyProofBasis) paths
    provenEdge = (source, target, edgeLab
        { dgl_type = setProof (Proven (globDecompRule $ getEdgeId edge)
                                      proof_basis)
            $ dgl_type edgeLab
        , dglPending = True
        , dgl_origin = DGLinkProof })
    in changesDGH newGr [DeleteEdge edge, InsertEdge provenEdge]

{- auxiliary function for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: Node -> (DGraph, ProofBasis)
                        -> [LEdge DGLinkLab]
                        -> (DGraph, ProofBasis)
-- for each path an unproven localThm edge is inserted
globDecompForOneEdgeAux target (dgraph, proof_basis) path =
  case path of
    [] -> error "globDecompForOneEdgeAux"
    (node, tar, lbl) : rpath -> let
      lbltype = dgl_type lbl
      isHiding = isHidingDef lbltype
      morphismPath = if isHiding then rpath else path
      morphism = fromMaybe
        (error "globDecomp: could not determine morphism of new edge")
        $ calculateMorphismOfPath morphismPath
      defEdgesToTarget = filter
        (\ (s, _, l) -> s == node && isGlobalDef (dgl_type l)
        && dgl_morphism l == morphism)
        $ innDG dgraph target
      newEdgeLbl = defDGLink morphism
        (if isHiding then hidingThm tar $ dgl_morphism lbl
            else if isGlobalDef lbltype then globalThm else localThm)
        DGLinkProof
      newEdge = (node, target, newEdgeLbl)
      in case defEdgesToTarget of
      (_, _, dl) : _ | not isHiding
             -> (dgraph, addEdgeId proof_basis $ dgl_id dl)
      _ | node == target && isInc (getRealDGLinkType newEdgeLbl)
               && isGlobalDef lbltype
             -> (dgraph, addEdgeId proof_basis $ dgl_id lbl)
      _ -> case tryToGetEdge newEdge dgraph of
        Nothing -> let
          newGraph = changeDGH dgraph $ InsertEdge newEdge
          finalEdge = case getLastChange newGraph of
            InsertEdge final_e -> final_e
            _ -> error "Proofs.Global.globDecompForOneEdgeAux"
          in (newGraph, addEdgeId proof_basis $ getEdgeId finalEdge)
        Just e -> (dgraph, addEdgeId proof_basis $ getEdgeId e)

globSubsumeFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globSubsumeFromList ln globalThmEdges libEnv =
    let dgraph = lookupDGraph ln libEnv
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        nextDGraph = foldl
            (globSubsumeAux libEnv) dgraph finalGlobalThmEdges
    in Map.insert ln nextDGraph libEnv

-- | tries to apply global subsumption to all unproven global theorem edges
globSubsume :: LibName -> LibEnv -> LibEnv
globSubsume ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        globalThmEdges = labEdgesDG dgraph
    in globSubsumeFromList ln globalThmEdges libEnv

-- auxiliary function for globSubsume (above) the actual implementation
globSubsumeAux :: LibEnv -> DGraph -> LEdge DGLinkLab -> DGraph
globSubsumeAux libEnv dgraph ledge@(src, tgt, edgeLab) =
  let morphism = dgl_morphism edgeLab
      filteredPaths = filterPathsByMorphism morphism $ filter (noPath ledge)
                    $ getAllGlobPathsBetween dgraph src tgt
      proofbasis = selectProofBasis dgraph ledge filteredPaths
  in if not (nullProofBasis proofbasis) || isIdentityEdge ledge libEnv dgraph
   then
     let globSubsumeRule = DGRuleWithEdge "Global-Subsumption"
           $ getEdgeId ledge
         newEdge = (src, tgt, edgeLab
               { dgl_type = setProof (Proven globSubsumeRule proofbasis)
                   $ dgl_type edgeLab
               , dgl_origin = DGLinkProof })
         newDGraph = changesDGH dgraph [DeleteEdge ledge, InsertEdge newEdge]
     in groupHistory dgraph globSubsumeRule newDGraph
   else dgraph
