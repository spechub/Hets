{- |
Module      :  $Header$
Description :  utility functions for edges of development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
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

{- | change the given DGraph with the given DGChange.
     To notice that, before inserting an edge, the edge ID will be given by 
     calling initEdgeID if necessary.
-}
changeDG :: DGraph -> DGChange -> DGraph
changeDG g c = case c of
    InsertNode n -> insLNodeDG n g
    DeleteNode n -> delLNodeDG n g
    InsertEdge e -> let 
                    l = initEdgeID e g 
                    in 
                    insLEdgeDG l g
    DeleteEdge e -> delLEdgeDG e g
    SetNodeLab _ n -> fst $ labelNodeDG n g    

{- | initialize the edge id before it's inserted, but if it already contains
     valid id, then do nothing -}
initEdgeID :: LEdge DGLinkLab -> DGraph -> LEdge DGLinkLab
initEdgeID (src, tgt, linklab) g 
    | dgl_id linklab == defaultEdgeID = (src, tgt, linklab{dgl_id = [getNewEdgeID g]})
    | otherwise = (src, tgt, linklab)    

{- | change the given DGraph with a list of DGChange
-}
changesDG :: DGraph -> [DGChange] -> DGraph/home/ken/workspace
changesDG = foldl' changeDG

{- | change the given DGraph with given DGChange and return a new DGraph and
     the processed DGChange as well.
-}
updateDGAndChange :: DGraph -> DGChange -> (DGraph, DGChange)
updateDGAndChange g c = case c of
    InsertNode n -> (insLNodeDG n g, InsertNode n)
    DeleteNode n -> (delLNodeDG n g, DeleteNode n)
    InsertEdge e -> let
                    newEdge = initEdgeID e g
                    in 
                    (insLEdgeDG newEdge g, InsertEdge newEdge)
    DeleteEdge e -> (delLEdgeDG e g, DeleteEdge e)
    SetNodeLab _ n -> let (newG, o) = labelNodeDG n g in (newG, SetNodeLab o n)

{- | change the given DGraph with a list of DGChange, but the processed
DGChanges are kept and in a reverted way for the history element.
-}
updateDGAndChanges :: DGraph -> [DGChange] -> (DGraph, [DGChange])
updateDGAndChanges g [] = (g, [])
updateDGAndChanges g (x:xs) = (auxGraph, newChange:auxChanges)
        where 
        (newGraph, newChange) = updateDGAndChange g x
        (auxGraph, auxChanges) = updateDGAndChanges newGraph xs
    
{- | apply the proof history to the given DGraph to make it go back to 
     previous one.
-}
applyProofHistory :: ProofHistory  -> DGraph -> DGraph
applyProofHistory h c =  setProofHistoryDG
			 h
			 (changesDG c $ concatMap snd $ reverse h )

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
    elem (InsertEdge newEdge) changes || elem newEdge (labEdgesDG dgraph)

{- | try to get the given edge from the given DGraph or the given list of
     DGChange to advoid dupplicate inserting of an edge
-}
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
                find (\e -> e==newEdge) (labEdgesDG dgraph)

{- | try to insert an edge into the given dgraph, if the edge exists, the to
be inserted edge's id would be added into the existing edge.-}
insertDGLEdge :: LEdge DGLinkLab -- ^ the to be inserted edge
              -> DGraph -> [DGChange] -> (DGraph, [DGChange])
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

{- | get the edge id out of a given edge -}
getEdgeID :: LEdge DGLinkLab -> EdgeID
getEdgeID (_, _, label) = dgl_id label

            
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
    edgesOfType = [edge | edge <- filter (liftE isType) (labEdgesDG dgraph)]
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
    outEdges = outDG dgraph src
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
    edgesOfTypes =
        [ edge | edge@(source, _, lbl) <- innDG dgraph tgt
               , tgt /= source, types $ dgl_type lbl, notElem edge path ]
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
  [path ++ [edge]| edge <- edgesOfType]
    ++(concat
        [getAllPathsOfTypeFromAux (path ++ [edge]) dgraph nextSrc isType|
         (edge,nextSrc) <- nextStep])
  where
    edgesOfType = 
        [ edge | edge@(_, target, _) <- outDG dgraph src
               , target /= src, isType edge, notElem edge path ]
    nextStep = [(edge,tgt)| edge@(_,tgt,_) <- edgesOfType, tgt /= src]


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
                 -> [EdgeID]
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
                    -> [EdgeID]
selectProofBasisAux _ _ [] = []
selectProofBasisAux dg ledge (path:list) =
    if not (roughElem ledge b) then {- OK, no cyclic proof -} b
     else selectProofBasisAux dg ledge list
    where b = calculateProofBasis dg path []

{- | calculates the proofBasis of the given path,
 i.e. (recursively) close the list of DGLinkLabs under the relation
 'is proved using'. If a DGLinkLab has proof status LeftOpen,
 look up in the development graph for its current status -}
calculateProofBasis :: DGraph -> [LEdge DGLinkLab] -> [EdgeID]
                        -> [EdgeID]
calculateProofBasis _ [] acc = acc
calculateProofBasis dg (ledge@(_,_,label):list) acc =
  if roughElem ledge acc
    then calculateProofBasis dg list acc
    else
     case (getOneStepProofBasis dg label) of
       Just proof_basis -> 
            let
            pbEdges = map (\edge_id->getDGLEdgeWithIDsForSure edge_id dg) 
                          proof_basis
            in
            calculateProofBasis dg (pbEdges++list) ((dgl_id label):acc)
       Nothing -> calculateProofBasis dg list ((dgl_id label):acc)

{- | try to get the proof basis of the given linklab according to the
     given DGraph.
-}
getOneStepProofBasis :: DGraph -> DGLinkLab -> Maybe [EdgeID]
getOneStepProofBasis dgraph label =
  case (getDGLinkLabWithIDs (dgl_id label) dgraph) of
       Nothing -> error ((show $ dgl_id label) ++ "Proofs.EdgeUtils.getOneStepProofBasis")
       Just e -> tryToGetProofBasis e

{- | return the proof basis if the given linklab is a proven edge, 
     otherwise Nothing.
-}
tryToGetProofBasis :: DGLinkLab -> Maybe [EdgeID]
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
  let (inEdges', _, _, outEdges') = safeContextDG "adoptEdges" dgraph oldNode
      inEdges = map ( \ (l, v) -> (v, oldNode, l)) inEdges'
      outEdges = map ( \ (l, v) -> (oldNode, v, l)) outEdges'
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

getAllOpenNodeGoals :: [DGNodeLab] -> [DGNodeLab]
getAllOpenNodeGoals = filter hasOpenGoals

------------------------
-- debug functions 
------------------------
{- | similar to a show function of an ledge but only prints the 
     necessary parts out.
-}
trace_edge :: LEdge DGLinkLab -> String
trace_edge (src, tgt, label) = " ("++(show src)++"->"++(show tgt)
                               ++" of id "++ (show $ dgl_id label)
                               ++" with prove status: "
                               ++(trace_edge_status label)++") ->"

{- | return a string describing the given path consisting of a list of ledge.
-}
trace_path :: [LEdge DGLinkLab] -> String
trace_path = concat . map trace_edge 

{- | return a string containing a simple telling of the status of the 
     given linklab.
-}
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

{- | show the given list of paths.
-}
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
      hidingEdges = filter (liftE isHidingEdge) $ labEdgesDG dgraph
      
{- | return a warning text if the given node has incoming hiding edge,
     otherwise just an empty string.
-}
addHasInHidingWarning :: DGraph -> Node -> String
addHasInHidingWarning dgraph n 
     | hasIncomingHidingEdge dgraph n =
           "< Warning: this node has incoming hiding links ! >\n"
     | otherwise = ""      

{- | return src node of the given edge.
-}
getLEdgeSrc :: LEdge b -> Node
getLEdgeSrc (n, _, _) = n 
