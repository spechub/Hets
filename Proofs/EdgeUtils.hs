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

import Comorphisms.LogicGraph
import Logic.Grothendieck
import Static.DevGraph
import Common.Result
import qualified Common.Lib.SizedList as SizedList
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (elfilter)
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Exception (assert)

-- | negate change
negateChange :: DGChange -> DGChange
negateChange change = case change of
      InsertNode x -> DeleteNode x
      DeleteNode x -> InsertNode x
      InsertEdge x -> DeleteEdge x
      DeleteEdge x -> InsertEdge x
      SetNodeLab old (node, new) -> SetNodeLab new (node, old)

flatHistory :: SizedList.SizedList HistElem -> [DGChange]
flatHistory h = if SizedList.null h then [] else
  (case SizedList.head h of
    HistElem c -> [c]
    HistGroup _ l -> flatHistory l) ++ flatHistory (SizedList.tail h)

contraryRedo :: SizedList.SizedList HistElem -> SizedList.SizedList HistElem
contraryRedo = SizedList.map $ \ he -> case he of
  HistElem c -> HistElem $ negateChange c
  HistGroup r l -> HistGroup r $ SizedList.reverse $ contraryRedo l

undoHistStep :: DGraph -> (DGraph, [DGChange])
undoHistStep dg = let h = proofHistory dg in
  if SizedList.null h then (dg, []) else let
  he = SizedList.head h
  (ndg, cs) = case he of
    HistElem c -> let (dg2, nc) = updateDGOnly dg $ negateChange c in
       (dg2 { proofHistory = SizedList.tail h }, [nc])
    HistGroup _ l -> let
     (dg2, ncs) = mapAccumL (\ g _ -> undoHistStep g)
        dg { proofHistory = SizedList.append l $ SizedList.tail h }
        $ SizedList.toList l
     in (dg2, concat ncs)
  in (ndg { redoHistory = SizedList.cons he $ redoHistory dg }, cs)

redoHistStep :: DGraph -> (DGraph, [DGChange])
redoHistStep dg = let h = redoHistory dg in
  if SizedList.null h then (dg, []) else
      let he = SizedList.head h
          cs = reverse $ flatHistory $ SizedList.singleton $ he
          (ndg, ncs) = updateDGAndChanges dg cs
      in (ndg { proofHistory = SizedList.cons he $ proofHistory dg
              , redoHistory = SizedList.tail h }, ncs)

-- | apply the reversed changes to the graph and add them to the history
applyProofHistory :: SizedList.SizedList HistElem -> DGraph -> DGraph
applyProofHistory l = applyReverseHistory $ reverseHistory l

applyReverseHistory :: SizedList.SizedList HistElem -> DGraph -> DGraph
applyReverseHistory l dg = if SizedList.null l then dg else
  applyReverseHistory (SizedList.tail l) $ case SizedList.head l of
    HistElem c -> changeDGH dg c
    HistGroup r h -> let dg2 = applyReverseHistory h dg in
      groupHistory dg r dg2

-- | change the given DGraph with a list of changes
changesDGH :: DGraph -> [DGChange] -> DGraph
changesDGH = foldl' changeDGH

-- | empty redo stack by moving redo changes and their reverses to the history
undoRedo :: DGraph -> DGraph
undoRedo g = let
  rh = redoHistory g
  he1 = HistGroup (DGRule "RedoRedo") $ SizedList.reverse rh
  he2 = HistGroup (DGRule "UndoRedo") $ contraryRedo rh
  he3 = HistGroup (DGRule "LeftOverRedo") $ SizedList.fromList [he2, he1]
  in if SizedList.null rh then g else g
      { proofHistory = SizedList.cons he3 $ proofHistory g
      , redoHistory = SizedList.empty }

-- | change the given DGraph and the history with the given DGChange.
changeDGH :: DGraph -> DGChange -> DGraph
changeDGH g c = let (ng, nc) = updateDGOnly g c in
  addToProofHistoryDG (HistElem nc) $ undoRedo ng

-- | change the given DGraph with a list of DGChange
updateDGAndChanges :: DGraph -> [DGChange] -> (DGraph, [DGChange])
updateDGAndChanges = mapAccumL updateDGOnly

{- | change the given DGraph with given DGChange and return a new DGraph and
     the processed DGChange as well. -}
updateDGOnly :: DGraph -> DGChange -> (DGraph, DGChange)
updateDGOnly g c =
  case c of
    InsertNode n -> (insLNodeDG n g, InsertNode n)
    DeleteNode n -> (delLNodeDG n g, DeleteNode n)
    InsertEdge e -> let (newEdge, ng) = insLEdgeDG e g in
      (ng, InsertEdge newEdge)
    DeleteEdge e -> (delLEdgeDG e g, DeleteEdge e)
    SetNodeLab _ n -> let (newG, o) = labelNodeDG n g in
      (newG, SetNodeLab o n)

-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------

isProven :: DGLinkType -> Bool
isProven edge = case edge of
    GlobalDef -> True
    LocalDef  -> True
    _ -> case thmLinkStatus edge of
           Just (Proven _ _) -> True
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

isHidingThm :: DGLinkType -> Bool
isHidingThm edge = case edge of
    HidingThm _ _ -> True
    _ -> False

isUnprovenHidingThm :: DGLinkType -> Bool
isUnprovenHidingThm lt = case lt of
    HidingThm _ LeftOpen -> True
    _ -> False

isFreeEdge :: DGLinkType -> Bool
isFreeEdge edge = case edge of
    FreeDef _ -> True
    _ -> False

isCofreeEdge :: DGLinkType -> Bool
isCofreeEdge edge = case edge of
    CofreeDef _ -> True
    _ -> False

-- ----------------------------------------------------------------------------
-- other methods on edges
-- ----------------------------------------------------------------------------

eqLEdge :: (DGLinkLab -> DGLinkLab -> Bool) -> LEdge DGLinkLab
          -> LEdge DGLinkLab -> Bool
eqLEdge f (v, w, l) (v2, w2, l2) = v == v2 && w == w2 && f l l2

noPath :: LEdge DGLinkLab -> [LEdge DGLinkLab] -> Bool
noPath e l = case l of
    [e2] -> not $ eqLEdge eqDGLinkLabById e e2
    _ -> True

{- | try to get the given edge from the given DGraph or the given list of
     DGChange to advoid duplicate inserting of an edge. -}
tryToGetEdge :: LEdge DGLinkLab -> DGraph -> Maybe (LEdge DGLinkLab)
tryToGetEdge (src, tgt, lb) dgraph = fmap (\ l -> (src, tgt, l))
  $ find (eqDGLinkLabContent lb) $ Tree.getLEdges src tgt $ dgBody dgraph

{- | try to insert an edge into the given dgraph, if the edge exists, the to
be inserted edge's id would be added into the existing edge. -}
insertDGLEdge :: LEdge DGLinkLab -- ^ the to be inserted edge
              -> DGraph -> DGraph
insertDGLEdge edge dgraph =
  case tryToGetEdge edge dgraph of
    Nothing -> changeDGH dgraph $ InsertEdge edge
    Just ne ->
        if elem (getEdgeId edge) [defaultEdgeId, getEdgeId ne]
        then dgraph
        else error "Proofs.EdgeUtils.insertDGLEdge"

{- | get the edge id out of a given edge -}
getEdgeId :: LEdge DGLinkLab -> EdgeId
getEdgeId (_, _, label) = dgl_id label

-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------

getAllPathsOfTypeFromGoalList :: DGraph -> (DGLinkType -> Bool)
                              -> [LEdge DGLinkLab] -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFromGoalList dgraph isType ls = concat
    [concat (map (getAllPathsOfTypeBetween dgraph isType source) targets) |
     source <- sources]
    where
      sources = Set.toList $ Set.fromList $ map (\ (s, _, _) -> s) ls
      targets = Set.toList $ Set.fromList $ map (\ (_, t, _) -> t) ls

{- | returns all paths consisting of edges of the given type in the given
   development graph-}
getAllPathsOfType :: DGraph -> (DGLinkType -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfType dgraph isType =
    getAllPathsOfTypeFromGoalList dgraph isType $ labEdgesDG dgraph

-- determines the morphism of a given path
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath p = case p of
  (_, _, lbl) : r -> let morphism = dgl_morphism lbl in
    if null r then Just morphism else do
       rmor <- calculateMorphismOfPath r
       resultToMaybe $ compInclusion logicGraph morphism rmor
  [] -> error "calculateMorphismOfPath"

{- | returns all paths from the given list whose morphism is equal to the
   given one -}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
                      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths =
  [path | path <- paths, calculateMorphismOfPath path == Just morphism]

{- | returns all paths consisting of global edges only
   or of one local edge followed by any number of global edges -}
getAllLocGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllLocGlobPathsBetween dgraph src tgt =
  locGlobPaths ++ globPaths
  where
    outEdges = outDG dgraph src
    locEdges = [(edge, target)
               | edge@(_,target,_) <- filter (liftE isLocalEdge) outEdges]
    locGlobPaths = concat
                   [map ([edge] ++)
                   $ getAllGlobPathsBetween dgraph node tgt
                    | (edge, node) <- locEdges]
    globPaths = getAllGlobPathsBetween dgraph src tgt

{- | returns all paths of globalDef edges or globalThm edges
   between the given source and target node -}
getAllGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypeBetween dgraph isGlobalEdge src tgt

{- | returns all cyclic paths consisting of edges of the given type between the
   given two nodes -}
getAllPathsOfTypeBetween :: DGraph -> (DGLinkType -> Bool) -> Node
                         -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeBetween dgraph isType src tgt =
    Tree.getPathsTo src tgt
    $ elfilter (isType . dgl_type)
    $ dgBody dgraph

-- | return all non-cyclic paths starting from the given node
getAllPathsOfTypeFrom :: DGraph -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFrom dgraph src =
   Tree.getPaths src $ dgBody dgraph

-- ----------------------------------------
-- methods to check and select proof basis
-- ----------------------------------------

checkEdgeIds :: DGraph -> Maybe [EdgeId]
checkEdgeIds dg =
    let pBl = map (\ (_, _, l) -> dgl_id l) $ labEdges $ dgBody dg
        pBs = Set.fromList pBl
        pBl2 = Set.toList pBs
    in case pBl \\ pBl2 of
         [] -> if Set.member defaultEdgeId pBs
               then Just [defaultEdgeId] else Nothing
         l -> Just l

{- | determines all proven paths in the given list and tries to select a
   proof basis from these (s. selectProofBasisAux);
   if this fails the same is done for the rest of the given paths, i.e.
   for the unproven ones -}
selectProofBasis :: DGraph -> LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                 -> ProofBasis
selectProofBasis dg ledge paths = let
  (provenPaths, unprovenPaths) = partition (all $ liftE isProven) paths
  pBl = map (\ (_, _, l) ->
               (dgl_id l, proofBasis $ tryToGetProofBasis l))
              $ labEdges $ dgBody dg
  rel = assert (checkEdgeIds dg == Nothing &&
                all (\ (e, pB) -> not (Set.member e pB)) pBl) $
        Rel.toMap $ Rel.transClosure $ Rel.fromDistinctMap
        $ Map.fromList $ filter (not . Set.null . snd) pBl
  in selectProofBasisAux rel ledge $ provenPaths ++ unprovenPaths

{- | selects the first path that does not form a proof cycle with the given
 label (if such a path exits) and returns the labels of its edges -}
selectProofBasisAux :: Map.Map EdgeId (Set.Set EdgeId) -> LEdge DGLinkLab
                    -> [[LEdge DGLinkLab]] -> ProofBasis
selectProofBasisAux _ _ [] = emptyProofBasis
selectProofBasisAux rel ledge (path : list) =
    if roughElem ledge b then selectProofBasisAux rel ledge list
       else b {- OK, no cyclic proof -}
    where b = calculateProofBasis rel path

{- | calculates the proofBasis of the given path,
 i.e. (recursively) close the list of DGLinkLabs under the relation
 'is proved using'. If a DGLinkLab has proof status LeftOpen,
 look up in the development graph for its current status -}
calculateProofBasis :: Map.Map EdgeId (Set.Set EdgeId) -> [LEdge DGLinkLab]
                    -> ProofBasis
calculateProofBasis rel = ProofBasis . foldr
    (\ (_, _, l) -> let eid = dgl_id l in Set.insert eid
     . Set.union (Map.findWithDefault Set.empty eid rel))
    Set.empty

{- | return the proof basis if the given linklab is a proven edge,
     otherwise Nothing. -}
tryToGetProofBasis :: DGLinkLab -> ProofBasis
tryToGetProofBasis label = case dgl_type label of
    GlobalThm (Proven _ pB) _ _ -> pB
    LocalThm (Proven _ pB) _ _ -> pB
    HidingThm _ (Proven _ pB) -> pB
    _ -> emptyProofBasis

invalidateProof :: DGLinkType -> DGLinkType
invalidateProof t = case t of
    GlobalThm _ c _ -> GlobalThm LeftOpen c LeftOpen
    LocalThm _ c _ -> LocalThm LeftOpen c LeftOpen
    HidingThm m _ -> HidingThm m LeftOpen
    FreeThm m _ -> FreeThm m LeftOpen
    _ -> t

{- | adopts the edges of the old node to the new node -}
adoptEdges :: DGraph -> Node -> Node -> DGraph
adoptEdges dgraph oldNode newNode =
  if oldNode == newNode then dgraph else
  let (inEdges', _, _, outEdges') = safeContextDG "adoptEdges" dgraph oldNode
      inEdges = map ( \ (l, v) -> (v, oldNode, l)) inEdges'
      outEdges = map ( \ (l, v) -> (oldNode, v, l)) outEdges'
      newIn = map (adoptEdgesAux newNode True) inEdges
      newOut = map (adoptEdgesAux newNode False) outEdges
      allChanges = map DeleteEdge (inEdges ++ outEdges)
                   ++ map InsertEdge (newIn ++ newOut)
  in changesDGH dgraph allChanges

{- | auxiliary method for adoptEdges -}
adoptEdgesAux :: Node -> Bool -> LEdge DGLinkLab -> LEdge DGLinkLab
adoptEdgesAux node areIngoingEdges (src,tgt,edgelab) =
  let (newSrc, newTgt) = if src == tgt then (node, node) else (src, tgt)
  in if areIngoingEdges then (newSrc, node, edgelab)
     else (node, newTgt, edgelab)

getAllOpenNodeGoals :: [DGNodeLab] -> [DGNodeLab]
getAllOpenNodeGoals = filter hasOpenGoals

{- | return a warning text if the given node has incoming hiding edge,
     otherwise just an empty string. -}
addHasInHidingWarning :: DGraph -> Node -> String
addHasInHidingWarning dgraph n = if labelHasHiding $ labDG dgraph n then
           "< Warning: this node has incoming hiding links ! \n" ++
           "  The theory shown here may be too weak. \n" ++
           "  Use the normal form of the node instead. >\n"
      else ""
