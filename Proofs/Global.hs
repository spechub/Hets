{- |
Module      :  $Header$
Description :  global proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

global proof rules for development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
todo for Jorina:

   - bei GlobDecomp hinzufügen:
     zusätzlich alle Pfade K<--theta-- M --sigma-->N in den aktuellen
     Knoten N, die mit einem HidingDef anfangen, und danach nur GlobalDef
     theta ist der Signaturmorphismus des HidingDef's (geht "falsch rum")
     sigma ist die Komposition der Signaturmorphismen auf dem restl. Pfad
     für jeden solchen Pfad: einen HidingThm theta einfügen. sigma ist
     der normale Morphismus (wie bei jedem anderen Link)
     siehe auch Seite 302 des CASL Reference Manual
-}

module Proofs.Global (globSubsume, globDecomp, globDecompAux, globDecompFromList, globSubsumeFromList) where

import Data.Graph.Inductive.Graph

import Logic.Grothendieck
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


{- applies global decomposition to the list of edges given (global theorem edges)
   if possible, if empty list is given then to all unproven global theorems -}
globDecompFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
globDecompFromList ln globalThmEdges proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        finalGlobalThmEdges = filter (liftE isUnprovenGlobalThm) globalThmEdges
        (newDGraph, newHistoryElem)= globDecompAux dgraph finalGlobalThmEdges 
                                     ([],[])
    in mkResultProofStatus ln proofStatus newDGraph newHistoryElem

{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp ::LIB_NAME -> LibEnv -> LibEnv
globDecomp ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        globalThmEdges = filter (liftE isUnprovenGlobalThm) $ labEdges dgraph
    in globDecompFromList ln globalThmEdges proofStatus 

{- applies global decomposition to all unproven global theorem edges
   if possible -}
--globDecomp :: LIB_NAME -> LibEnv -> LibEnv
--globDecomp ln proofStatus =
--  let dgraph = lookupDGraph ln proofStatus
--      globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
--      (newDGraph, newHistoryElem) = globDecompAux dgraph globalThmEdges ([],[])
--        (finalDGraph, finalHistoryElem)
--            = removeSuperfluousInsertions newDGraph newHistoryElem
--  in mkResultProofStatus ln proofStatus newDGraph newHistoryElem
        --finalDGraph finalHistoryElem

{- removes all superfluous insertions from the list of changes as well as
   from the development graph  (i.e. insertions of edges that are
   equivalent to edges or paths resulting from the other insertions) -}
removeSuperfluousInsertions :: DGraph -> ([DGRule],[DGChange])
                                 -> (DGraph,([DGRule],[DGChange]))
removeSuperfluousInsertions dgraph (rules,changes)
  = (newDGraph,(rules,newChanges))
  where
    localThms = [edge | (InsertEdge edge)
                        <- filter isLocalThmInsertion changes]
    (newDGraph, localThmsToInsert)
        = removeSuperfluousEdges dgraph localThms
    newChanges = (filter (not.isLocalThmInsertion) changes)
                     ++ [InsertEdge edge | edge <- localThmsToInsert]

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
  globDecompForOneEdgeAux dgraph edge [] paths
  where
    defEdgesToSource = [e | e@(_, tgt, lbl) <- labEdges dgraph,
                        isDefEdge (dgl_type lbl) && tgt == source]
    paths = map (\e -> [e,edge]) defEdgesToSource ++ [[edge]]
    --getAllLocOrHideGlobDefPathsTo dgraph (getSourceNode edge) []
--    paths = [(node, path++(edge:[]))| (node,path) <- pathsToSource]

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange] ->
                           [[LEdge DGLinkLab]] -> (DGraph,[DGChange])
{- if the list of paths is empty from the beginning, nothing is done
   otherwise the unprovenThm edge is replaced by a proven one -}
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes [] =
--  if null changes then (dgraph, changes)
  -- else
     if isDuplicate provenEdge dgraph changes
            then updateWithOneChange (DeleteEdge edge) dgraph changes
	    --(deLLEdge edge dgraph, ((DeleteEdge edge):changes))
      else updateWithChanges [DeleteEdge edge, InsertEdge provenEdge] dgraph changes
	   --((insEdge provenEdge (deLLEdge edge dgraph)),
           --((DeleteEdge edge):((InsertEdge provenEdge):changes)))
  where
    (GlobalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    proofBasis = getInsertedEdges changes
    provenEdge = (source,
                  target,
                  DGLink {dgl_morphism = dgl_morphism edgeLab,
                          dgl_type =
                            (GlobalThm (Proven (GlobDecomp edge) proofBasis)
                             conservativity conservStatus),
                          dgl_origin = DGProof}
                  )
-- for each path an unproven localThm edge is inserted
globDecompForOneEdgeAux dgraph edge@(_,target,_) changes
 (path:list) =
  if isDuplicate newEdge dgraph changes-- list
    then globDecompForOneEdgeAux dgraph edge changes list
   else globDecompForOneEdgeAux newGraph edge newChanges list
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
                dgl_origin = DGProof})
    globalEdge = (node,
                  target,
                  DGLink {dgl_morphism = morphism,
                          dgl_type = (GlobalThm LeftOpen
                                      None LeftOpen),
                          dgl_origin = DGProof}
                 )
    localEdge = (node,
                 target,
                 DGLink {dgl_morphism = morphism,
                         dgl_type = (LocalThm LeftOpen
                                     None LeftOpen),
                         dgl_origin = DGProof}
               )
    (newGraph, newChanges) = updateWithOneChange (InsertEdge newEdge) dgraph changes
    -- newGraph = insEdge newEdge dgraph
    -- newChanges = ((InsertEdge newEdge):changes)

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


globSubsume :: LIB_NAME -> LibEnv -> LibEnv
globSubsume ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        globalThmEdges  = filter (liftE isUnprovenGlobalThm) $ labEdges dgraph
    in globSubsumeFromList ln globalThmEdges libEnv

-- applies global subsumption to all unproven global theorem edges if possible
--globSubsume :: LIB_NAME -> LibEnv -> LibEnv
--globSubsume ln libEnv =
--  let dgraph = lookupDGraph ln libEnv
--      globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
--    {- the previous 'nub' is (probably) not needed, because it is
--       (or should be) checked for duplicate edge insertions -}
--      (nextDGraph, nextHistoryElem) =
--          globSubsumeAux libEnv dgraph ([],[]) globalThmEdges
--  in mkResultProofStatus ln libEnv nextDGraph nextHistoryElem

{- auxiliary function for globSubsume (above)
   the actual implementation -}
globSubsumeAux :: LibEnv ->  DGraph -> ([DGRule],[DGChange]) ->
                  [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux _ dgraph historyElement [] = (dgraph, historyElement)
globSubsumeAux libEnv dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if not (null proofBasis) || isIdentityEdge ledge libEnv dgraph
   then
     if isDuplicate newEdge dgraph changes then
	let
	(newGraph, newChanges) = updateWithOneChange (DeleteEdge ledge) dgraph changes
	in
	globSubsumeAux libEnv newGraph (newRules, newChanges) list 
        --globSubsumeAux libEnv (deLLEdge ledge dgraph)
        --  (newRules,(DeleteEdge ledge):changes) list
      else
	let
	(newGraph, newChanges) = updateWithChanges [DeleteEdge ledge, InsertEdge newEdge] dgraph changes
	in
	globSubsumeAux libEnv newGraph (newRules, newChanges) list
        -- globSubsumeAux libEnv (insEdge newEdge (deLLEdge ledge dgraph))
        --  (newRules,(DeleteEdge ledge):((InsertEdge newEdge):changes)) list
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
                       dgl_origin = DGProof}
               )
    newRules = (GlobSubsumption ledge):rules

-- ---------------------------------------------------------------------------
-- methods for the extension of globDecomp (avoid insertion ofredundant edges)
-- ---------------------------------------------------------------------------

{- returns all paths consisting of local theorem links whose src and tgt nodes
   are contained in the given list of nodes -}
localThmPathsBetweenNodes ::  DGraph -> [Node] -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodes _ [] = []
localThmPathsBetweenNodes dgraph ns = localThmPathsBetweenNodesAux dgraph ns ns

{- auxiliary method for localThmPathsBetweenNodes -}
localThmPathsBetweenNodesAux :: DGraph -> [Node] -> [Node]
                             -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodesAux _ [] _ = []
localThmPathsBetweenNodesAux dgraph (node:srcNodes) tgtNodes =
  concatMap (getAllPathsOfTypeBetween dgraph isUnprovenLocalThm node) tgtNodes
  ++ localThmPathsBetweenNodesAux dgraph srcNodes tgtNodes

{- combines each of the given paths with matching edges from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
combinePathsWithEdges :: [[LEdge DGLinkLab]] -> [LEdge DGLinkLab]
                      -> [[LEdge DGLinkLab]]
combinePathsWithEdges paths = concatMap (combinePathsWithEdge paths)

{- combines the given path with each matching edge from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
combinePathsWithEdge :: [[LEdge DGLinkLab]] -> LEdge DGLinkLab
                     -> [[LEdge DGLinkLab]]
combinePathsWithEdge [] _ = []
combinePathsWithEdge (path:paths) edge@(src,_,_) =
  case path of
    [] -> combinePathsWithEdge paths edge
    _ :_ -> let (_, tgt, _) = last path in
            if tgt == src
              then (path ++ [edge]) : combinePathsWithEdge paths edge
                else combinePathsWithEdge paths edge

{- todo: choose a better name for this method...
   returns for each of the given paths a pair consisting of the last edge
   contained in the path and - as a triple - the src, tgt and morphism of the
   complete path
   if there is an empty path in the given list or the morphsim cannot be
   calculated, it is simply ignored -}
calculateResultingEdges :: [[LEdge DGLinkLab]]
                        -> [(LEdge DGLinkLab, (Node, Node, GMorphism))]
calculateResultingEdges [] = []
calculateResultingEdges (path : paths) =
  case path of
    [] -> calculateResultingEdges paths
    (src, _, _) : _ ->
       case calculateMorphismOfPath path of
         Nothing -> calculateResultingEdges paths
         Just morphism -> (lst, (src, tgt, morphism)) :
                          calculateResultingEdges paths
       where lst@(_, tgt, _) = last path

{- removes from the given list every edge for which there is already an
   equivalent edge or path (i.e. an edge or path with the same src, tgt and
   morphsim) -}
removeSuperfluousEdges :: DGraph -> [LEdge DGLinkLab]
                       -> (DGraph,[LEdge DGLinkLab])
removeSuperfluousEdges dgraph [] = (dgraph,[])
removeSuperfluousEdges dgraph es
  = removeSuperfluousEdgesAux dgraph es
        (calculateResultingEdges combinedPaths) []
  where
    localThmPaths
        = localThmPathsBetweenNodes dgraph (map ( \ (s, _, _) -> s) es)
    combinedPaths = combinePathsWithEdges localThmPaths es

{- auxiliary method for removeSuperfluousEdges -}
removeSuperfluousEdgesAux :: DGraph -> [LEdge DGLinkLab]
                          -> [(LEdge DGLinkLab,(Node,Node,GMorphism))]
                          -> [LEdge DGLinkLab] -> (DGraph,[LEdge DGLinkLab])
removeSuperfluousEdgesAux dgraph [] _ edgesToInsert= (dgraph,edgesToInsert)
removeSuperfluousEdgesAux dgraph ((edge@(src,tgt,edgeLab)):list)
                          resultingEdges edgesToInsert =
  if not (null equivalentEdges)
     then removeSuperfluousEdgesAux
          newDGraph list newResultingEdges edgesToInsert
      else removeSuperfluousEdgesAux
           dgraph list resultingEdges (edge:edgesToInsert)
  where
    equivalentEdges
        = [e | e <- resultingEdges,(snd e) == (src,tgt,dgl_morphism edgeLab)]
    newResultingEdges = [e | e <- resultingEdges,(fst e) /= edge]
    newDGraph = deLLEdge edge dgraph

{- returns true, if the given change is an insertion of an local theorem edge,
   false otherwise -}
isLocalThmInsertion :: DGChange -> Bool
isLocalThmInsertion change
  = case change of
      InsertEdge edge -> liftE isLocalThm edge
      _ -> False
