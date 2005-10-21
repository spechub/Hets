{- |
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

utility functions for edges of a development graphs.

-}

module Proofs.EdgeUtils where

import Data.List(nub)
import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map
import Common.Utils

delLEdge :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdge (v, w, l) g = case match v g of
    (Just(p, v', l', s), g') -> (p, v', l', filter (/= (l, w)) s) & g'
    _ -> g 

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

  
isIdentityEdge :: LEdge DGLinkLab -> LibEnv -> DGraph -> Bool
isIdentityEdge (src,tgt,edgeLab) libEnv dgraph =
  if isDGRef nodeLab then 
    case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> isIdentityEdge 
                              (dgn_node nodeLab,tgt,edgeLab) libEnv refDgraph
      Nothing -> False
   else src == tgt && 
        dgl_morphism edgeLab == ide Grothendieck (dgn_sign nodeLab)

  where nodeLab = lab' $ safeContext "Proofs.EdgeUtils.isIdentityEdge" 
                  dgraph src

{- returns the DGLinkLab of the given LEdge -}
getLabelOfEdge :: (LEdge b) -> b
getLabelOfEdge (_,_,label) = label

-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------

{- returns all paths consisting of edges of the given type in the given
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


{- returns a list of all proven global paths of the given morphism between
   the given source and target node-}
getAllGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
                                          -> [[LEdge DGLinkLab]]
getAllGlobPathsOfMorphismBetween dgraph morphism src tgt = 
  filterPathsByMorphism morphism allPaths

  where 
      allPaths = getAllGlobPathsBetween dgraph src tgt


{- returns all paths from the given list whose morphism is equal to the
   given one-}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
                      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths = 
  [path| path <- paths, (calculateMorphismOfPath path) == (Just morphism)]


{- returns all paths consisting of global edges only
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


{- returns all paths of globalDef edges or globalThm edges 
   between the given source and target node -}
getAllGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypesBetween dgraph (liftOr isGlobalDef isGlobalThm) src tgt []


{- returns all paths consiting of edges of the given type between the
   given node -}
getAllPathsOfTypeBetween :: DGraph -> (LEdge DGLinkLab -> Bool) -> Node
                            -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeBetween dgraph isType src tgt =
  getAllPathsOfTypesBetween dgraph isType src tgt []


{- returns all paths consisting of edges of the given types between
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

{- returns all insertions of edges from the given list of changes -}
getInsertedEdges :: [DGChange] -> [LEdge DGLinkLab]
getInsertedEdges [] = []
getInsertedEdges (change:list) = 
  case change of
    (InsertEdge edge) -> edge:(getInsertedEdges list)
    _ -> getInsertedEdges list

-- ----------------------------------------
-- methods to check and select proof basis
-- ----------------------------------------

{- determines all proven paths in the given list and tries to selet a
   proof basis from these (s. selectProofBasisAux);
   if this fails the same is done for the rest of the given paths, i.e.
   for the unproven ones -}
selectProofBasis :: LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                 -> [LEdge DGLinkLab]
selectProofBasis ledge paths =
  if null provenProofBasis then selectProofBasisAux ledge unprovenPaths
   else provenProofBasis

  where 
    provenPaths = filterProvenPaths paths
    provenProofBasis = selectProofBasisAux ledge provenPaths
    unprovenPaths = [path | path <- paths, notElem path provenPaths]

{- selects the first path that does not form a proof cycle with the given
 label (if such a path exits) and returns the labels of its edges -}
selectProofBasisAux :: LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                    -> [LEdge DGLinkLab]
selectProofBasisAux _ [] = []
selectProofBasisAux ledge (path:list) =
    if notProofCycle ledge path then nub (calculateProofBasis path)
     else selectProofBasisAux ledge list


{- calculates the proofBasis of the given path,
 i.e. the list of all DGLinkLabs the proofs of the edges contained in the path
 are based on, plus the DGLinkLabs of the edges themselves;
 duplicates are not removed here, but in the calling method
 selectProofBasisAux -}
calculateProofBasis :: [LEdge DGLinkLab] -> [LEdge DGLinkLab]
calculateProofBasis [] = []
calculateProofBasis (ledge:list) =
  ledge:((getProofBasis ledge)++(calculateProofBasis list))


{- returns the proofBasis contained in the given DGLinkLab -}
getProofBasis :: LEdge DGLinkLab -> [LEdge DGLinkLab]
getProofBasis (_,_,label) =
  case dgl_type label of 
    (GlobalThm (Proven _ proofBasis) _ _) -> proofBasis
    (LocalThm (Proven _ proofBasis) _ _) -> proofBasis
    _ -> []


{- returns all proven paths from the given list -}
filterProvenPaths :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterProvenPaths [] = []
filterProvenPaths (path:list) =
  if (and [isProven edge| edge <- path]) then path:(filterProvenPaths list)
   else filterProvenPaths list

{- opposite of isProofCycle -}
notProofCycle :: LEdge DGLinkLab -> [LEdge DGLinkLab] -> Bool
notProofCycle ledge = not.(isProofCycle ledge)

{- checks if the given label is contained in the ProofBasis of one of the
   edges of the given path -}
isProofCycle :: LEdge DGLinkLab -> [LEdge DGLinkLab] -> Bool
isProofCycle _ [] = False
isProofCycle ledge (e:path) =
  if (elemOfProofBasis ledge e) then True else (isProofCycle ledge path)

{- checks if the given label is contained in the ProofBasis of the given 
   edge -}
elemOfProofBasis :: LEdge DGLinkLab -> (LEdge DGLinkLab) -> Bool
elemOfProofBasis ledge (_,_,dglink) =
  case dgl_type dglink of 
    (GlobalThm (Proven _ proofBasis) _ _) -> elem ledge proofBasis
    (LocalThm (Proven _ proofBasis) _ _) -> elem ledge proofBasis
    _ -> False


{- adopts the edges of the old node to the new node -}
adoptEdges :: DGraph -> Node -> Node -> (DGraph, [DGChange])
adoptEdges dgraph oldNode newNode = 
  let ingoingEdges = inn dgraph oldNode
      outgoingEdges = [outEdge| outEdge <- out dgraph oldNode,
                                not (elem outEdge ingoingEdges)]
      (auxGraph, changes) = adoptEdgesAux dgraph ingoingEdges newNode True
      (finalGraph, furtherChanges) 
          = adoptEdgesAux auxGraph outgoingEdges newNode False
  in (finalGraph, changes ++ furtherChanges)

{- auxiliary method for adoptEdges -}
adoptEdgesAux :: DGraph -> [LEdge DGLinkLab] -> Node -> Bool
                     -> (DGraph,[DGChange])
adoptEdgesAux dgraph [] _ _ = (dgraph,[])
adoptEdgesAux dgraph (oldEdge@(src,tgt,edgelab):list) node areIngoingEdges =
  (finalGraph, [DeleteEdge oldEdge,InsertEdge newEdge]++furtherChanges)

  where
    (newSrc,newTgt) = if src == tgt then (node,node) else (src,tgt)
    newEdge = if areIngoingEdges then (newSrc,node,edgelab)
                else (node,newTgt,edgelab)
    auxGraph = insEdge newEdge (delLEdge oldEdge dgraph)
    (finalGraph,furtherChanges) 
        = adoptEdgesAux auxGraph list node areIngoingEdges
