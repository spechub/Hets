{- |
Module      :  $Header$
Description :  global proof rules for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

global proof rules for development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

module Proofs.Global (globSubsume, globDecomp, globDecompAux, globDecompFromList, globSubsumeFromList) where

import Data.Graph.Inductive.Graph

--import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Syntax.AS_Library

import Proofs.EdgeUtils
import Proofs.StatusUtils

import qualified Data.List as STD_List

--import Debug.Trace

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

	{-
	  to solve the library border
	  but it is limited in such a case that the referenced library is
	  completely proved...(???)
	  solved: to get the referenced node until its original one
	-}
	toBeCheckedSourceNodes = 
            STD_List.nub [src|(src, _, _)<-finalGlobalThmEdges]
	(auxDGraph, auxChanges) = 
            updateCurrentDGraphWithReferencedLib dgraph
						 proofStatus
						 toBeCheckedSourceNodes
						 []
	(newDGraph, (rules, newChanges))= 
            globDecompAux auxDGraph finalGlobalThmEdges ([],[])
{-
        (newDGraph, newHistoryElem)= globDecompAux dgraph finalGlobalThmEdges 
                                     ([],[])
    in mkResultProofStatus ln proofStatus newDGraph newHistoryElem
-}
    in mkResultProofStatus ln proofStatus newDGraph 
			   (rules, auxChanges++newChanges) 

-- | update current dgraph by checking whether the given nodelist contains
-- referenced node or not. If so, the related part in referenced library would
-- be shown in current library too.
updateCurrentDGraphWithReferencedLib :: DGraph -- ^ current DGraph 
				     -> LibEnv -- ^ lib environment
				     -> [Node] -- ^ to be checked nodes
				     -> [DGChange] -- ^ dgchange list 
				     -> (DGraph, [DGChange]) 
updateCurrentDGraphWithReferencedLib dgraph _ [] changes = (dgraph, changes)
updateCurrentDGraphWithReferencedLib dgraph libEnv (oneNode:others) changes =
     let 
     (auxDGraph, auxChanges) = updateDGraphWithRefLibForOneNode dgraph 
								libEnv
								oneNode 
								changes
     in
     updateCurrentDGraphWithReferencedLib auxDGraph libEnv others auxChanges
     
-- | update the given dgraph by checking whether the given node is a
-- referenced node or not. If so, the related part in referenced library would
-- be shown in current library too.
updateDGraphWithRefLibForOneNode :: DGraph -- ^ current DGraph
				 -> LibEnv -- ^ lib environment
				 -> Node -- ^ to be checked node
				 -> [DGChange] -- ^ dgchange list 
				 -> (DGraph, [DGChange])
updateDGraphWithRefLibForOneNode dgraph libEnv node changes = 
     case (isDGRef nodeLab) of
	  True -> let
		  (nodeEdgePairs, refLibName) = 
			getReferencedNodeEdgePairs  libEnv nodeLab
		  {-
		  refLibName = dgn_libname nodeLab
		  refDGraph = lookupDGraph refLibName libEnv
		  nodeEdgePairs = lpre refDGraph (dgn_node nodeLab)
		   nodeEdgePairs = 
		     [(src, edgeLab)| (src, tgt, edgeLab)<-labEdges refDGraph,
				      tgt == (dgn_node nodeLab)]
		  -}
		  in
		  -- trace (show $ map fst nodeEdgePairs) $ 
	          tryToInsertRefNodeEdgePairs dgraph libEnv refLibName 
					      changes node nodeEdgePairs		  
	  False -> (dgraph, changes)
     where
     nodeLab = lab' $ safeContext 
		      "Proofs.Global.updateDGraphWithRefLibForOneNode"
		      dgraph node

getReferencedNodeEdgePairs :: LibEnv -> DGNodeLab -> 
			      ([(Node, DGLinkLab)], LIB_NAME)
getReferencedNodeEdgePairs libEnv nodeLab = 
     let
     refLibName = dgn_libname nodeLab
     refDGraph = lookupDGraph refLibName libEnv
     refNode = dgn_node nodeLab
     refNodeLab = lab' $ safeContext
			 "Proofs.Global.getReferencedNodeEdgePairs"
			 refDGraph refNode
     in
     case (isDGRef refNodeLab) of
	  True -> getReferencedNodeEdgePairs libEnv refNodeLab
	  False -> (lpre refDGraph refNode, refLibName)

-- | try to insert the given node edge pair list into current 
-- DGraph with given info
tryToInsertRefNodeEdgePairs :: DGraph -- ^ current DGraph
			    -> LibEnv -- ^ the lib enviroment
			    -> LIB_NAME -- ^ referenced lib name
			    -> [DGChange] -- ^ change list
			    -> Node -- ^ target in current dgraph
			    -> [(Node, DGLinkLab)]  -- ^ to be inserted pairs
			    -> (DGraph, [DGChange])
tryToInsertRefNodeEdgePairs dgraph _ _ changes _ [] = (dgraph, changes)
tryToInsertRefNodeEdgePairs dgraph libEnv refLibName changes node (pair:rest) =
     let
     (auxDGraph, auxChanges) = 
         tryToInsertOneRefNodeEdgePair dgraph libEnv refLibName changes node pair
     in
     tryToInsertRefNodeEdgePairs auxDGraph libEnv refLibName auxChanges node rest    

-- | try to insert one given node edge pair into current 
-- DGraph with given info
tryToInsertOneRefNodeEdgePair :: DGraph -- ^ current DGraph
			    -> LibEnv -- ^ the lib enviroment
			    -> LIB_NAME -- ^ referenced lib name
			    -> [DGChange] -- ^ change list
			    -> Node -- ^ target in current dgraph
			    -> (Node, DGLinkLab)  -- ^ to be inserted pair
			    -> (DGraph, [DGChange])
tryToInsertOneRefNodeEdgePair dgraph libEnv refLibName
			      changes absTgt (refSrc, edgeLab) =
     let
     (absSrc, auxDGraph, auxChanges) = 
         tryToInsertRefNode dgraph libEnv refLibName refSrc
     (finalDGraph, auxChanges2) =
         insertDGLEdge (absSrc, absTgt, edgeLab{dgl_id = defaultEdgeID})
		       auxDGraph []
     in
     (finalDGraph, changes++auxChanges++auxChanges2)

--     in
  --   (auxDGraph, changes++auxChanges)

-- | try to get the referenced node which refers to a non-referenced node in a
-- referenced library
getPreOriginalNode :: LibEnv -> LIB_NAME -> Node -> (LIB_NAME, Node, DGNodeLab)
getPreOriginalNode libEnv refLibName refNode =
     let
     refDG = lookupDGraph refLibName libEnv
     refNodeLab = lab' $ safeContext "Proofs.Global.getOriginalNode"
			 refDG refNode
     in
     case (isDGRef refNodeLab) of 
	  False -> (refLibName, refNode, refNodeLab)
	  True -> let
		  nextRefLibName = dgn_libname refNodeLab
		  nextRefNode = dgn_node refNodeLab
		  in
		  getPreOriginalNode libEnv nextRefLibName nextRefNode

-- | try to insert the given referenced node into current DGraph
tryToInsertRefNode :: DGraph -- ^ current DGraph
		   -> LibEnv -- ^ the lib enviroment
		   -> LIB_NAME -- ^ referenced lib name
		   -> Node -- ^ to be inserted referenced node 
		   -> (Node, DGraph, [DGChange])
tryToInsertRefNode dgraph libEnv refLibName refNode = 
     let
     (auxRefLibName, auxRefNode, auxRefNodeLab) = 
	getPreOriginalNode libEnv refLibName refNode
     maybeNode = tryToGetRefNodeWithRefNode dgraph auxRefLibName auxRefNode
     in
     case maybeNode of
	  -- already existed?
          Just absNode -> (absNode, dgraph, [])
	  -- otherwise?
	  Nothing -> 
	       let
	       newNodeID = getNewNode dgraph
	       {-
	       question: if the referenced node refers to another node
	       too, how can it be solved?
	       solved, the original node would be found ;)
	       -}
	       finalNodeLab = 
                     DGRef {
			   dgn_name = dgn_name auxRefNodeLab,
			   dgn_libname = auxRefLibName,
			   dgn_node = auxRefNode,
			   dgn_theory = dgn_theory auxRefNodeLab,
			   dgn_nf = dgn_nf auxRefNodeLab,
			   dgn_sigma = dgn_sigma auxRefNodeLab
		     }
	       (auxDGraph, auxChanges) = 
                     updateWithOneChange (InsertNode (newNodeID, finalNodeLab))
					 dgraph
					 []
	       in
	       (newNodeID, auxDGraph, auxChanges)

-- try to get Node with its referenced node.
tryToGetRefNodeWithRefNode :: DGraph -- ^ current DGraph
		   -> LIB_NAME -- ^ referenced lib name
		   -> Node -- ^ to be searched referenced node
		   -> Maybe Node
tryToGetRefNodeWithRefNode dgraph refLN refNode =
     case matchNode of
	  Nothing -> Nothing
	  Just (foundNode, _) -> Just foundNode
     where
     allRefNodes = filter (\(_, x) -> isDGRef x) $ labNodes dgraph
     matchNode = STD_List.find (\(_, x) -> (dgn_libname x == refLN)
				            && (dgn_node x == refNode))
                                allRefNodes

{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp ::LIB_NAME -> LibEnv -> LibEnv
globDecomp ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        globalThmEdges = filter (liftE isUnprovenGlobalThm) $ labEdges dgraph
	--xxx = checkDuplicateRefNode dgraph
    in --trace ("the possiblely duplicate nodes are: " ++ show xxx)$  
       globDecompFromList ln globalThmEdges proofStatus


{-
checkDuplicateRefNode :: DGraph -> [Node]
checkDuplicateRefNode dgraph = 
    let
    allNodes = labNodes dgraph
    allRefNodes = filter (\(_, nlab) -> isDGRef nlab) allNodes    
    in
    checkAux allRefNodes
    where
    matchNodes :: LNode DGNodeLab -> [LNode DGNodeLab] -> [Node]
    matchNodes (_, nlab) ls = map fst $ filter (\(_, x) -> (dgn_libname x == dgn_libname nlab) && (dgn_node x == dgn_node nlab)) ls
    checkAux :: [LNode DGNodeLab] -> [Node]
    checkAux [] = []
    checkAux (x:xs) = 
       let 
       dns = matchNodes x xs
       in
       if trace ((show $ dgn_libname $ snd x)++": "++(show $ dgn_node $ snd x)) $ (length dns) > 0 then (fst x):(checkAux xs)
			   else checkAux xs
-}


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
{-
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
-}

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
    defEdgesToSource = [e | e@(_, tgt, lbl) <- labEdges dgraph,
                        isDefEdge (dgl_type lbl) && tgt == source]
    paths = map (\e -> [e,edge]) defEdgesToSource ++ [[edge]]
    --getAllLocOrHideGlobDefPathsTo dgraph (getSourceNode edge) []
--    paths = [(node, path++(edge:[]))| (node,path) <- pathsToSource]

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange] ->
                           [[LEdge DGLinkLab]] -> 
			   [EdgeID] -> 
			   --[LEdge DGLinkLab] -> 
			   (DGraph,[DGChange])
{- if the list of paths is empty from the beginning, nothing is done
   otherwise the unprovenThm edge is replaced by a proven one -}
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes 
			[] proof_basis =
--  if null changes then (dgraph, changes)
  -- else
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

-- ---------------------------------------------------------------------------
-- methods for the extension of globDecomp (avoid insertion ofredundant edges)
-- ---------------------------------------------------------------------------

{- returns all paths consisting of local theorem links whose src and tgt nodes
   are contained in the given list of nodes -}
{-
localThmPathsBetweenNodes ::  DGraph -> [Node] -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodes _ [] = []
localThmPathsBetweenNodes dgraph ns = localThmPathsBetweenNodesAux dgraph ns ns
-}

{- auxiliary method for localThmPathsBetweenNodes -}
{-
localThmPathsBetweenNodesAux :: DGraph -> [Node] -> [Node]
                             -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodesAux _ [] _ = []
localThmPathsBetweenNodesAux dgraph (node:srcNodes) tgtNodes =
  concatMap (getAllPathsOfTypeBetween dgraph isUnprovenLocalThm node) tgtNodes
  ++ localThmPathsBetweenNodesAux dgraph srcNodes tgtNodes
-}

{- combines each of the given paths with matching edges from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
{-
combinePathsWithEdges :: [[LEdge DGLinkLab]] -> [LEdge DGLinkLab]
                      -> [[LEdge DGLinkLab]]
combinePathsWithEdges paths = concatMap (combinePathsWithEdge paths)
-}

{- combines the given path with each matching edge from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
{-
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
-}

{- todo: choose a better name for this method...
   returns for each of the given paths a pair consisting of the last edge
   contained in the path and - as a triple - the src, tgt and morphism of the
   complete path
   if there is an empty path in the given list or the morphsim cannot be
   calculated, it is simply ignored -}
{-
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
-}

{- removes from the given list every edge for which there is already an
   equivalent edge or path (i.e. an edge or path with the same src, tgt and
   morphsim) -}
{-
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
-}

{- auxiliary method for removeSuperfluousEdges -}
{-
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
-}

{- returns true, if the given change is an insertion of an local theorem edge,
   false otherwise -}
{-
isLocalThmInsertion :: DGChange -> Bool
isLocalThmInsertion change
  = case change of
      InsertEdge edge -> liftE isLocalThm edge
      _ -> False
-}

