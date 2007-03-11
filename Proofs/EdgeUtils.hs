{- |
Module      :  $Header$
Description :  utility functions for edges of development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

utility functions for edges of development graphs
-}

module Proofs.EdgeUtils where

import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Data.Graph.Inductive.Graph
import Data.List

--import Debug.Trace

deLLEdge :: LEdge DGLinkLab -> DGraph -> DGraph
deLLEdge e@(v, w, l) g = case match v g of
    (Just(p, v', l', s), g') ->
        let (ls, rs) = partition ((l, w) ==) s in
        case ls of
          [] -> error $ "deLLEdge no edge: " ++ show e
          [_] -> (p, v', l', rs) & g'
          _ -> error $ "deLLEdge multiple edges: " ++ show e
    _ -> error $ "deLLEdge no node for edge: " ++ show e

insLEdge :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdge e@(v, w, l) g = case match v g of
    (Just(p, v', l', s), g') ->
        let ls = filter ((l, w) ==) s in
        case ls of
          [] -> (p, v', l', (l, w) : s) & g'
          _ -> error $ "insLEdge multiple edge: " ++ show e
    _ -> error $ "insLEdge no node for edge: " ++ show e

delLNode :: LNode DGNodeLab -> DGraph -> DGraph
delLNode n@(v, l) g = case match v g of
    (Just(p, _, l', s), g') ->
       if l' == l then
           if null p && null s then g'
           else error $ "delLNode remaining edges: " ++ show (p ++ s)
       else error $ "delLNode wrong label: " ++ show n
    _ -> error $ "delLNode no such node: " ++ show n

insLNode :: LNode DGNodeLab -> DGraph -> DGraph
insLNode n@(v, _) g =
    if gelem v g then error $ "insLNode " ++ show v else insNode n g

labelNode :: LNode DGNodeLab -> DGraph -> (DGraph, DGNodeLab)
labelNode (v, l) g = case match v g of
    (Just(p, _, o, s), g') -> ((p, v, l, s) & g', o)
    _ -> error $ "labelNode no such node: " ++ show v

changeDG :: DGraph -> DGChange -> DGraph
changeDG g c = case c of
    InsertNode n -> insLNode n g
    DeleteNode n -> delLNode n g
    InsertEdge e -> let 
		    l = initEdgeID e g 
		    in 
		    insLEdge l g
    DeleteEdge e -> deLLEdge e g
    SetNodeLab _ n -> fst $ labelNode n g    

{- | initialize the edge id before it's inserted, but if it already contains
     valid id, then do nothing -}
initEdgeID :: LEdge DGLinkLab -> DGraph -> LEdge DGLinkLab
initEdgeID (src, tgt, linklab) g 
    | dgl_id linklab == defaultEdgeID = (src, tgt, linklab{dgl_id = [getNewEdgeID g]})
    | otherwise = (src, tgt, linklab)    

changesDG :: DGraph -> [DGChange] -> DGraph
changesDG = foldl' changeDG

updateDGAndChange :: DGraph -> DGChange -> (DGraph, DGChange)
updateDGAndChange g c = case c of
    InsertNode n -> (insLNode n g, InsertNode n)
    DeleteNode n -> (delLNode n g, DeleteNode n)
    InsertEdge e -> let
		    newEdge = initEdgeID e g
		    in 
		    (insLEdge newEdge g, InsertEdge newEdge)
    DeleteEdge e -> (deLLEdge e g, DeleteEdge e)
    SetNodeLab _ n -> let (newG, o) = labelNode n g in (newG, SetNodeLab o n)

updateDGAndChanges :: DGraph -> [DGChange] -> (DGraph, [DGChange])
updateDGAndChanges g [] = (g, [])
updateDGAndChanges g (x:xs) = (auxGraph, newChange:auxChanges)
	where 
	(newGraph, newChange) = updateDGAndChange g x
	(auxGraph, auxChanges) = updateDGAndChanges newGraph xs
    

applyProofHistory :: ProofHistory  -> GlobalContext -> GlobalContext
applyProofHistory h c = c { devGraph = changesDG (devGraph c) $ concatMap snd
                                       $ reverse h
                          , proofHistory = h }

-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------

isProven :: DGLinkType -> Bool
isProven edge = case edge of
    GlobalDef -> True
    LocalDef  -> True
    _ -> case thmLinkStatus edge of 
           Just Proven{} -> True
           _ -> False

isDefEdge :: DGLinkType -> Bool
isDefEdge edge = case edge of
    GlobalDef -> True
    LocalDef  -> True
    HidingDef -> True
    _ -> False
 
isGlobalEdge :: DGLinkType -> Bool
isGlobalEdge edge = case edge of
    GlobalDef -> True
    GlobalThm _ _ _ -> True
    _ -> False

isLocalEdge :: DGLinkType -> Bool
isLocalEdge edge = case edge of
    LocalDef  -> True
    LocalThm _ _ _ -> True
    _ -> False

isGlobalThm :: DGLinkType -> Bool
isGlobalThm edge = case edge of
    GlobalThm _ _ _ -> True
    _ -> False

isLocalThm :: DGLinkType -> Bool
isLocalThm edge = case edge of
    LocalThm _ _ _ -> True
    _ -> False

isUnprovenGlobalThm :: DGLinkType -> Bool
isUnprovenGlobalThm lt = case lt of
    GlobalThm LeftOpen _ _ -> True
    _ -> False

isUnprovenLocalThm :: DGLinkType -> Bool
isUnprovenLocalThm lt = case lt of
    LocalThm LeftOpen _ _ -> True
    _ -> False

isHidingEdge :: DGLinkType -> Bool
isHidingEdge edge = case edge of
    HidingDef -> True
    HidingThm _ _ -> True  
    _ -> False

isHidingDef :: DGLinkType -> Bool
isHidingDef lt = case lt of
    HidingDef -> True
    _ -> False

isHidingThm :: DGLinkType -> Bool
isHidingThm edge = case edge of
    HidingThm _ _ -> True  
    _ -> False

isUnprovenHidingThm :: DGLinkType -> Bool
isUnprovenHidingThm lt = case lt of
    HidingThm _ LeftOpen -> True
    _ -> False

-- ----------------------------------------------------------------------------
-- other methods on edges
-- ----------------------------------------------------------------------------

{- | returns true, if an identical edge is already in the graph or
     marked to be inserted, false otherwise -}
isDuplicate :: LEdge DGLinkLab -> DGraph -> [DGChange] -> Bool
isDuplicate newEdge dgraph changes =
    elem (InsertEdge newEdge) changes || elem newEdge (labEdges dgraph)

tryToGetEdge :: LEdge DGLinkLab -> DGraph -> 
		[DGChange] -> Maybe (LEdge DGLinkLab)
tryToGetEdge newEdge dgraph changes =
      case tryToGetEdgeFromChanges of 
	   (Just e) -> Just e
	   Nothing -> case tryToGetEdgeFromDGraph of
			   (Just e) -> Just e
			   Nothing -> Nothing
      where
      tryToGetEdgeFromChanges =
		find (\e -> e==newEdge) (getInsertedEdges changes)
      tryToGetEdgeFromDGraph = 
		find (\e -> e==newEdge) (labEdges dgraph)

{- | try to insert an edge into the given dgraph, if the edge exists, the to
be inserted edge's id would be added into the existing edge.-}
insertDGLEdge :: LEdge DGLinkLab -> -- ^ the to be inserted edge
		      DGraph ->
		      [DGChange] -> 
		      (DGraph, [DGChange])
insertDGLEdge edge@(_, _, edgeLab) dgraph changes =
      case (tryToGetEdge edge dgraph changes) of
	   Nothing -> updateWithChanges [InsertEdge edge] 
					dgraph
					changes  
	   Just e@(src, tgt, label) -> 
	     if (withoutValidID edge) 
	      then
		(dgraph, changes)
	      else
		let
		newEdge = (src, tgt, 
			   label{
				 dgl_id=((dgl_id label)++
				         (dgl_id edgeLab))
				})  
	        in
		updateWithChanges [DeleteEdge e, InsertEdge newEdge]
				   dgraph
				   changes

{- | check if the given edge doesn't contain valid id -}
withoutValidID :: LEdge DGLinkLab -> Bool
withoutValidID (_, _, label) = null $ dgl_id label

	    
-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------

getAllPathsOfTypeFromGoalList :: DGraph -> (DGLinkType -> Bool) 
                              -> [LEdge DGLinkLab] -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFromGoalList dgraph isType ls =
    concat
    [concat (map (getAllPathsOfTypeBetween dgraph isType source) targets) |
     source <- sources]
    where
      sources = nub $ map (\ (s, _, _) -> s) ls
      targets = nub $ map (\ (_, t, _) -> t) ls


{- | returns all paths consisting of edges of the given type in the given
   development graph-}
getAllPathsOfType :: DGraph -> (DGLinkType -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfType dgraph isType =
  concat
  [concat (map (getAllPathsOfTypeBetween dgraph isType source) targets) |
   source <- sources]
  where
    edgesOfType = [edge | edge <- filter (liftE isType) (labEdges dgraph)]
    sources = nub (map (\ (s, _, _) -> s) edgesOfType)
    targets = nub (map (\ (_, t, _) -> t) edgesOfType)

{- | returns a list of all proven global paths of the given morphism between
   the given source and target node-}
getAllGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
                                          -> [[LEdge DGLinkLab]]
getAllGlobPathsOfMorphismBetween dgraph morphism src tgt =
  filterPathsByMorphism morphism allPaths
  where
      allPaths = getAllGlobPathsBetween dgraph src tgt

{- | returns all paths from the given list whose morphism is equal to the
   given one-}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
                      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths =
  [path| path <- paths, (calculateMorphismOfPath path) == (Just morphism)]

{- | returns all paths consisting of global edges only
   or
   of one local edge followed by any number of global edges-}
getAllLocGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllLocGlobPathsBetween dgraph src tgt =
  locGlobPaths ++ globPaths
  where
    outEdges = out dgraph src
    locEdges = [(edge,target)|edge@(_,target,_) <-
                (filter (liftE isLocalEdge) outEdges)]
    locGlobPaths = concat
                   [map ([edge]++)
                   $ getAllPathsOfTypesBetween dgraph isGlobalEdge node tgt []
                    |  (edge, node) <- locEdges]
    globPaths = getAllPathsOfTypesBetween dgraph isGlobalEdge src tgt []

{- | returns all paths of globalDef edges or globalThm edges
   between the given source and target node -}
getAllGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypesBetween dgraph (liftOr isGlobalDef isGlobalThm) src tgt []

{- | returns all paths consisting of edges of the given type between the
   given node -}
getAllPathsOfTypeBetween :: DGraph -> (DGLinkType -> Bool) -> Node
                            -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeBetween dgraph isType src tgt =
  getAllPathsOfTypesBetween dgraph isType src tgt []

{- | returns all paths consisting of edges of the given types between
   the given nodes -}
getAllPathsOfTypesBetween :: DGraph -> (DGLinkType -> Bool) -> Node
                             -> Node -> [LEdge DGLinkLab]
                             -> [[LEdge DGLinkLab]]
getAllPathsOfTypesBetween dgraph types src tgt path =
  [edge:path| edge <- edgesFromSrc]
          ++ (concat
               [getAllPathsOfTypesBetween dgraph types src nextTgt (edge:path)|
               (edge,nextTgt) <- nextStep] )
  where
    inGoingEdges = inn dgraph tgt
    edgesOfTypes =
        [edge| edge <- filter (liftE types) inGoingEdges, notElem edge path]
    edgesFromSrc =
        [edge| edge@(source,_,_) <- edgesOfTypes, source == src]
    nextStep =
        [(edge, source)| edge@(source,_,_) <- edgesOfTypes, source /= src]

getAllPathsOfTypeFrom :: DGraph -> Node -> (LEdge DGLinkLab -> Bool)
                      -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFrom = getAllPathsOfTypeFromAux []

getAllPathsOfTypeFromAux :: [LEdge DGLinkLab] -> DGraph -> Node
                         -> (LEdge DGLinkLab -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFromAux path dgraph src isType =
  [path ++ [edge]| edge <- edgesFromSrc, notElem edge path && isType edge]
    ++(concat
        [getAllPathsOfTypeFromAux (path ++ [edge]) dgraph nextSrc isType|
         (edge,nextSrc) <- nextStep])
  where
    edgesFromSrc = out dgraph src
    nextStep = [(edge,tgt)| edge@(_,tgt,_) <- edgesFromSrc,
                tgt /= src && notElem edge path && isType edge]

-- --------------------------------------------------------------
-- methods to determine the inserted edges in the given dgchange
-- --------------------------------------------------------------

{- | returns all insertions of edges from the given list of changes -}
getInsertedEdges :: [DGChange] -> [LEdge DGLinkLab]
getInsertedEdges [] = []
getInsertedEdges (change:list) =
  case change of
    (InsertEdge edge) -> edge:(getInsertedEdges list)
    _ -> getInsertedEdges list

-- ----------------------------------------
-- methods to check and select proof basis
-- ----------------------------------------

{- | determines all proven paths in the given list and tries to select a
   proof basis from these (s. selectProofBasisAux);
   if this fails the same is done for the rest of the given paths, i.e.
   for the unproven ones -}
selectProofBasis :: DGraph -> LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                 -> [LEdge DGLinkLab]
selectProofBasis dg ledge paths =
  if null provenProofBasis then selectProofBasisAux dg ledge unprovenPaths
     else provenProofBasis
  where
    provenPaths = filterProvenPaths paths
    provenProofBasis = selectProofBasisAux dg ledge provenPaths
    unprovenPaths = filter (`notElem` provenPaths) paths

{- | selects the first path that does not form a proof cycle with the given
 label (if such a path exits) and returns the labels of its edges -}
selectProofBasisAux :: DGraph -> LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                    -> [LEdge DGLinkLab]
selectProofBasisAux _ _ [] = []
selectProofBasisAux dg ledge (path:list) =
    if not (roughElem ledge b) then {- OK, no cyclic proof -} b
     else selectProofBasisAux dg ledge list
    where b = calculateProofBasis dg path []

{- | calculates the proofBasis of the given path,
 i.e. (recursively) close the list of DGLinkLabs under the relation
 'is proved using'. If a DGLinkLab has proof status LeftOpen,
 look up in the development graph for its current status -}
calculateProofBasis :: DGraph -> [LEdge DGLinkLab] -> [LEdge DGLinkLab]
                        -> [LEdge DGLinkLab]
calculateProofBasis _ [] acc = acc
calculateProofBasis dg (ledge@(_,_,label):list) acc =
  if roughElem ledge acc
    then calculateProofBasis dg list acc
    else
     case (getOneStepProofBasis dg label) of
       Just proof_basis -> calculateProofBasis dg (proof_basis++list) (ledge:acc)
       Nothing -> calculateProofBasis dg list (ledge:acc)

{-
     case oneStepProofBasis label of
      Left proofBasis -> calculateProofBasis dg (proofBasis++list) (ledge:acc)
      Right True -> calculateProofBasis dg (curProofBasis++list) (ledge:acc)
      Right False -> calculateProofBasis dg list (ledge:acc)
  where curProofBasis =
         case lookup tgt (lsuc dg src) >>= (thmLinkStatus . dgl_type) of
           Just (Proven _ proofBasis) -> proofBasis
           _ -> []
-}

getOneStepProofBasis :: DGraph -> DGLinkLab -> Maybe [LEdge DGLinkLab]
getOneStepProofBasis dgraph label =
  case (getDGLinkLabWithIDs (dgl_id label) dgraph) of
       Nothing -> error "Proofs.EdgeUtils.getOneStepProofBasis"
       Just e -> tryToGetProofBasis e

tryToGetProofBasis :: DGLinkLab -> Maybe [LEdge DGLinkLab]
tryToGetProofBasis label = 
  case dgl_type label of
    (GlobalThm (Proven _ proofBasis) _ _) -> Just proofBasis
    (LocalThm (Proven _ proofBasis) _ _) -> Just proofBasis
    (HidingThm _ (Proven _ proofBasis)) -> Just proofBasis
    _ -> Nothing

{-
{- | calculate proof basis of a single edge
   Return either Left proof_basis, if there is one,
   or Right flag, where flag=True indicates a theorem link
-}
oneStepProofBasis :: DGLinkLab -> Either [LEdge DGLinkLab] Bool
oneStepProofBasis label =
  case dgl_type label of
    (GlobalThm (Proven _ proofBasis) _ _) -> Left proofBasis
    (LocalThm (Proven _ proofBasis) _ _) -> Left proofBasis
    (HidingThm _ (Proven _ proofBasis)) -> Left proofBasis
    (GlobalThm LeftOpen _ _) -> Right True
    (LocalThm LeftOpen _ _) -> Right True
    (HidingThm _ LeftOpen) -> Right True
    _ -> Right False  -- todo: also treat conservativity proof status
-}

{- | returns all proven paths from the given list -}
filterProvenPaths :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterProvenPaths = filter (all $ liftE isProven)

{- | adopts the edges of the old node to the new node -}
adoptEdges :: DGraph -> Node -> Node -> (DGraph, [DGChange])
adoptEdges dgraph oldNode newNode =
  if oldNode == newNode then (dgraph, []) else
  let inEdges = inn dgraph oldNode
      outEdges = out dgraph oldNode
      newIn = map (adoptEdgesAux newNode True) inEdges
      newOut = map (adoptEdgesAux newNode False) outEdges
      allChanges = map DeleteEdge (inEdges ++ outEdges)
                   ++ map InsertEdge (newIn ++ newOut)
  in (changesDG dgraph allChanges, allChanges)

{- | auxiliary method for adoptEdges -}
adoptEdgesAux :: Node -> Bool -> LEdge DGLinkLab -> LEdge DGLinkLab
adoptEdgesAux node areIngoingEdges (src,tgt,edgelab) =
  let (newSrc,newTgt) = if src == tgt then (node, node) else (src, tgt)
  in if areIngoingEdges then (newSrc, node, edgelab)
     else (node, newTgt, edgelab)

{- | adjusts a node whose label is changed -}
adjustNode :: DGraph -> LNode DGNodeLab -> (DGraph, [DGChange])
adjustNode dgraph newNode = 
  updateWithOneChange (SetNodeLab (error "adjustNode") newNode) dgraph []    
  {-
  let
      es = inn dgraph node ++ out dgraph node
      changes = map DeleteEdge es ++ [DeleteNode (node, oldLab),
                InsertNode (node, newLab)] ++ map InsertEdge es
      
      changes = [SetNodeLab newNode]
  in (changesDG dgraph changes, changes)
  -}

getAllOpenNodeGoals :: [DGNodeLab] -> [DGNodeLab]
getAllOpenNodeGoals = filter hasOpenGoals


--debugging functions

trace_edge :: LEdge DGLinkLab -> String
trace_edge (src, tgt, label) = " ("++(show src)++"->"++(show tgt)
			       ++" of id "++ (show $ dgl_id label)
			       ++" with prove status: "
			       ++(trace_edge_status label)++") ->"

trace_path :: [LEdge DGLinkLab] -> String
trace_path = concat . map trace_edge 

trace_edge_status :: DGLinkLab -> String
trace_edge_status label = 
    case (dgl_type label) of 
       (GlobalThm (Proven _ _) _ _) -> "global proven"
       (LocalThm (Proven _ _) _ _) -> "local proven"
       (HidingThm _ (Proven _ _)) -> "hiding proven"
       (LocalThm LeftOpen _ _) -> "local unproven"
       (GlobalThm LeftOpen _ _) -> "global unproven"
       GlobalDef -> "global def"
       LocalDef  -> "local def"
       HidingDef -> "hiding def" 
       _ -> "other unproven or proven"

trace_paths :: [[LEdge DGLinkLab]] -> String
trace_paths = pathWithNum 1 
	    where
	    pathWithNum :: Int -> [[LEdge DGLinkLab]] -> String
	    pathWithNum _ [] = ""
	    pathWithNum n (x:xs) = (show n ++ trace_path x++"\n") 
				++ pathWithNum (n+1) xs 


{- | update both the given devgraph and the changelist with a given change -}
updateWithOneChange :: DGChange -> DGraph -> [DGChange] -> (DGraph, [DGChange])
updateWithOneChange change dgraph changeList = (newGraph, newChange:changeList)
                    where
		    (newGraph, newChange) = updateDGAndChange dgraph change

{- | update both the given devgraph and the changelist with a list of given changes -}
updateWithChanges :: [DGChange] -> DGraph -> [DGChange] -> (DGraph, [DGChange])
updateWithChanges changes dgraph changeList = (newGraph, newChanges++changeList)
                  where
		  (newGraph, newChanges) = updateDGAndChanges dgraph changes

{- | check in the given dgraph if the given node has incoming hiding edges -}
hasIncomingHidingEdge :: DGraph -> Node -> Bool
hasIncomingHidingEdge dgraph node = any (\(_, tgt, _) -> node == tgt) hidingEdges
      where
      hidingEdges = filter (liftE isHidingEdge) $ labEdges dgraph
      

addHasInHidingWarning :: DGraph -> Node -> String
addHasInHidingWarning dgraph n 
     | hasIncomingHidingEdge dgraph n =
           "< Warning: this node has incoming hiding links ! >\n"
     | otherwise = ""      





