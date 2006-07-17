{- |
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

utility functions for edges of a development graphs.
-}

{- todo: also treat conservativity proof status in computation of proof basis
-}

module Proofs.EdgeUtils where

import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Data.Graph.Inductive.Graph
import Data.List

delLEdge :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdge e@(v, _, _) g = case match v g of
    (Just(p, v', l', s), g') ->
        let (ls, rs) = partition (\ (k, n) -> e == (v, n, k)) s in
        case ls of
          [] -> error $ "delLEdge no edge: " ++ show e
          [_] -> (p, v', l', rs) & g'
          _ -> error $ "delLEdge multiple edges: " ++ show e
    _ -> error $ "delLEdge no node for edge: " ++ show e

insLEdge :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdge e@(v, w, l) g = case match v g of
    (Just(p, v', l', s), g') ->
        let ls = filter (\ (k, n) -> e == (v, n, k)) s in
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
    if gelem v g then error $ "insLNode " ++ show n else insNode n g

changeDG :: DGraph -> DGChange -> DGraph
changeDG g c = case c of
    InsertNode n -> insLNode n g
    DeleteNode n -> delLNode n g
    InsertEdge e -> insLEdge e g
    DeleteEdge e -> delLEdge e g

changesDG :: DGraph -> [DGChange] -> DGraph
changesDG = foldl' changeDG

applyProofHistory :: ProofHistory  -> GlobalContext -> GlobalContext
applyProofHistory h c = c { devGraph = changesDG (devGraph c) $ concatMap snd 
                                       $ reverse h
                          , proofHistory = h }

-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------
isProven :: LEdge DGLinkLab -> Bool
isProven edge = isGlobalDef edge || isLocalDef edge
                || isProvenGlobalThm edge || isProvenLocalThm edge
                || isProvenHidingThm edge

isDefEdge :: LEdge DGLinkLab -> Bool
isDefEdge edge = isGlobalDef edge || isLocalDef edge || isHidingDef edge

isGlobalEdge :: LEdge DGLinkLab -> Bool
isGlobalEdge edge = isGlobalDef edge || isGlobalThm edge

isLocalEdge :: LEdge DGLinkLab -> Bool
isLocalEdge edge = isLocalDef edge || isLocalThm edge

isGlobalThm :: LEdge DGLinkLab -> Bool
isGlobalThm edge = isProvenGlobalThm edge || isUnprovenGlobalThm edge

isLocalThm :: LEdge DGLinkLab -> Bool
isLocalThm edge = isProvenLocalThm edge || isUnprovenLocalThm edge

isProvenGlobalThm :: LEdge DGLinkLab -> Bool
isProvenGlobalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (GlobalThm (Proven _ _) _ _) -> True
    _ -> False

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (GlobalThm LeftOpen _ _) -> True
    _ -> False

isProvenLocalThm :: LEdge DGLinkLab -> Bool
isProvenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm (Proven _ _) _ _) -> True
    _ -> False

isUnprovenLocalThm :: LEdge DGLinkLab -> Bool
isUnprovenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm LeftOpen _ _) -> True
    _ -> False

isHidingEdge :: LEdge DGLinkLab -> Bool
isHidingEdge edge = isHidingDef edge || isHidingThm edge

isHidingDef :: LEdge DGLinkLab -> Bool
isHidingDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    HidingDef -> True
    _ -> False

isHidingThm :: LEdge DGLinkLab -> Bool
isHidingThm edge = isProvenHidingThm edge || isUnprovenHidingThm edge

isProvenHidingThm :: LEdge DGLinkLab -> Bool
isProvenHidingThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (HidingThm _ (Proven _ _)) -> True
    _ -> False

isUnprovenHidingThm :: LEdge DGLinkLab -> Bool
isUnprovenHidingThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (HidingThm _ LeftOpen) -> True
    _ -> False

-- ----------------------------------------------------------------------------
-- other methods on edges
-- ----------------------------------------------------------------------------

{- | returns true, if an identical edge is already in the graph or
     marked to be inserted, false otherwise -}
isDuplicate :: LEdge DGLinkLab -> DGraph -> [DGChange] -> Bool
isDuplicate newEdge dgraph changes =
    elem (InsertEdge newEdge) changes || elem newEdge (labEdges dgraph)

{- | returns the DGLinkLab of the given LEdge -}
getLabelOfEdge :: (LEdge b) -> b
getLabelOfEdge (_,_,label) = label

-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------



getAllPathsOfTypeFromGoalList :: DGraph -> (LEdge DGLinkLab -> Bool) ->[LEdge DGLinkLab] -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFromGoalList dgraph isType ls =
    concat
    [concat (map (getAllPathsOfTypeBetween dgraph isType source) targets) |
     source <- sources]
    where 
      edgesOfType = [edge | edge <- ls]
      sources = nub (map getSourceNode edgesOfType)
      targets = nub (map getTargetNode edgesOfType)


{- | returns all paths consisting of edges of the given type in the given
   development graph-}
getAllPathsOfType :: DGraph -> (LEdge DGLinkLab -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfType dgraph isType =
  concat
  [concat (map (getAllPathsOfTypeBetween dgraph isType source) targets) |
   source <- sources]
  where
    edgesOfType = [edge | edge <- filter isType (labEdges dgraph)]
    sources = nub (map getSourceNode edgesOfType)
    targets = nub (map getTargetNode edgesOfType)

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
                (filter isLocalEdge outEdges)]
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

{- | returns all paths consiting of edges of the given type between the
   given node -}
getAllPathsOfTypeBetween :: DGraph -> (LEdge DGLinkLab -> Bool) -> Node
                            -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeBetween dgraph isType src tgt =
  getAllPathsOfTypesBetween dgraph isType src tgt []

{- | returns all paths consisting of edges of the given types between
   the given nodes -}
getAllPathsOfTypesBetween :: DGraph -> (LEdge DGLinkLab -> Bool) -> Node
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
        [edge| edge <- filter types inGoingEdges, notElem edge path]
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
calculateProofBasis dg (ledge@(src,tgt,label):list) acc =
  if roughElem ledge acc
    then calculateProofBasis dg list acc
    else
     case oneStepProofBasis label of
      Left proofBasis -> calculateProofBasis dg (proofBasis++list) (ledge:acc)
      Right True -> calculateProofBasis dg (curProofBasis++list) (ledge:acc)
      Right False -> calculateProofBasis dg list (ledge:acc)
  where curProofBasis =
         case lookup tgt (lsuc dg src) >>= (thmLinkStatus . dgl_type) of
           Just (Proven _ proofBasis) -> proofBasis
           _ -> []

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

{- | returns all proven paths from the given list -}
filterProvenPaths :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterProvenPaths = filter (all isProven)

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
adjustNode :: DGraph -> (Node, DGNodeLab) -> DGNodeLab -> (DGraph, [DGChange])
adjustNode dgraph (node,oldLab) newLab =
  let es = inn dgraph node ++ out dgraph node
      changes = map DeleteEdge es ++ [DeleteNode (node, oldLab),
                InsertNode (node, newLab)] ++ map InsertEdge es
   in (changesDG dgraph changes, changes)

--getAllNodeGoals :: LIB_NAME -> LibEnv -> [DGNodeLab]
--getAllNodeGoals ln libEnv = 
--                          let dgraph = lookupDgraph ln  libEnv
--                          in nodes dgraph  

getAllOpenNodeGoals :: [DGNodeLab] -> [DGNodeLab]
getAllOpenNodeGoals nodes =
                           filter hasOpenGoals nodes 
