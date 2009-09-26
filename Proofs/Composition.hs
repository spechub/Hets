{- |
Module      :  $Header$
Description :  Composition rules in the development graphs calculus
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Composition rules in the development graphs calculus.
  Follows Sect. IV:4.4 of the CASL Reference Manual, while combining
  several rules into one.
-}

module Proofs.Composition
    ( composition
    , compositionCreatingEdges
    , compositionFromList
    , compositionCreatingEdgesFromList
    ) where

import Proofs.EdgeUtils

import Static.DevGraph

import Logic.Grothendieck

import Common.Consistency
import Common.LibName
import qualified Common.Lib.Graph as Tree

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Data.List

compositionCreatingEdgesFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv
                                 -> LibEnv
compositionCreatingEdgesFromList libname ls proofStatus =
      let dgraph = lookupDGraph libname proofStatus
          pathsToCompose = filter ((> 1) . length) $
              getAllPathsOfTypeFromGoalList dgraph isGlobalThm ls
          newDGraph = compositionCreatingEdgesAux dgraph pathsToCompose
      in Map.insert libname newDGraph proofStatus

{- | creates new edges by composing all paths of global theorem edges
   in the current development graph. These new edges are proven global
   theorems with the morphism and the conservativity of the corresponding
   path. If a new edge is the proven version of a previsously existing
   edge, that edge is deleted. -}
compositionCreatingEdges :: LibName -> LibEnv -> LibEnv
compositionCreatingEdges libname proofStatus =
    let dgraph = lookupDGraph libname proofStatus
        allEdges = labEdgesDG dgraph
    in compositionCreatingEdgesFromList libname allEdges proofStatus

{- auxiliary method for compositionCreatingEdges -}
compositionCreatingEdgesAux :: DGraph -> [[LEdge DGLinkLab]] -> DGraph
compositionCreatingEdgesAux dgraph [] = dgraph
compositionCreatingEdgesAux dgraph (path : paths) =
 case calculateMorphismOfPath path of
   Nothing -> compositionCreatingEdgesAux dgraph paths
   Just _ -> let
    (src, _, _) = head path
    (_, tgt, _) = last path
    Just morph = calculateMorphismOfPath path
    cons = case getConservativityOfPath path of
             Mono -> if isTransportable morph then Mono else Cons
             c -> c
    newEdge = (src, tgt, DGLink
      { dgl_morphism = morph
      , dgl_type = ScopedLink Global
          (ThmLink (Proven (Composition path)
                   $ foldl addEdgeId emptyProofBasis $ map getEdgeId path))
          (ConsStatus cons None LeftOpen)
      , dgl_origin = DGLinkProof
      , dgl_id = defaultEdgeId })
    newDGraph = insertDGLEdge newEdge dgraph
    newDGraph2 = deleteRedundantEdges newDGraph newEdge
    in groupHistory dgraph (Composition path) newDGraph2

{- | this method is used by compositionCreatingEdgesAux.  It selects
all unproven global theorem edges in the given development graph that
have the same source, target, morphism and conservativity as the given
one. It then deletes them from the given graph and adds a
corresponding change -}
deleteRedundantEdges :: DGraph -> LEdge DGLinkLab -> DGraph
deleteRedundantEdges dgraph (src, tgt, labl) = let
    redundantEdges =
      [ (src, tgt, l) | l <- Tree.getLEdges src tgt $ dgBody dgraph
      , isUnprovenGlobalThm $ dgl_type l
      , dgl_morphism l == dgl_morphism labl
      , haveSameCons l labl ]
    haveSameCons :: DGLinkLab -> DGLinkLab -> Bool
    haveSameCons lab1 lab2 = case (dgl_type lab1, dgl_type lab2) of
          (ScopedLink Global (ThmLink LeftOpen) (ConsStatus cons1 _ status1),
           ScopedLink Global (ThmLink _) (ConsStatus cons2 _ status2)) ->
             cons1 == cons2 &&
             isProvenThmLinkStatus status1 == isProvenThmLinkStatus status2
          _ -> False
   in foldl deleteRedundantEdgesAux dgraph redundantEdges

{- auxiliary method for deleteRedundantEdgesAux -}
deleteRedundantEdgesAux :: DGraph -> LEdge DGLinkLab -> DGraph
deleteRedundantEdgesAux dgraph = changeDGH dgraph . DeleteEdge

-- | composition without creating new new edges
compositionFromList :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
compositionFromList libname glbThmEdge proofStatus = let
    dgraph = lookupDGraph libname proofStatus
    newDGraph = foldl compositionAux dgraph
      $ filter (liftE isGlobalThm) $ glbThmEdge
  in Map.insert libname newDGraph proofStatus

{- | gets all unproven global theorem edges in the current development graph
   and checks, if they are a composition of a global theorem path. If so,
   the edge is proven, with the corresponding path as its proof basis.
   If there is more than one path, the first of them is arbitrarily taken. -}
composition :: LibName -> LibEnv -> LibEnv
composition libname proofStatus =
  let dgraph = lookupDGraph libname proofStatus
      globalThmEdges = labEdgesDG dgraph
  in compositionFromList libname globalThmEdges proofStatus

{- | auxiliary method for composition -}
compositionAux :: DGraph -> LEdge DGLinkLab -> DGraph
compositionAux dgraph edge =
  case compositionForOneEdge dgraph edge of
    Nothing -> dgraph
    Just (newEdge, proofbasis) -> let
      newDGraph = changesDGH dgraph [DeleteEdge edge, InsertEdge newEdge]
      in groupHistory dgraph (Composition proofbasis) newDGraph

{- | checks for the given edges, if there is a path in the given
development graph that it is a composition of. If so, it is replaced
by a proven version with the path as its proof basis.  The method
returns Nothing if there is no such path or else the new edge and the
path. -}
compositionForOneEdge :: DGraph -> LEdge DGLinkLab
                      -> Maybe (LEdge DGLinkLab, [LEdge DGLinkLab])
compositionForOneEdge dgraph edge@(src,tgt,labl) =
  compositionForOneEdgeAux edge [path | path <- pathsOfMorphism,
                                 noPath edge path]
  where
    globThmPaths = getAllPathsOfTypeBetween dgraph isGlobalThm src tgt
    pathsOfMorphism = filterPathsByMorphism (dgl_morphism labl) globThmPaths

{- auxiliary method for compositionForOneEdge -}
compositionForOneEdgeAux :: LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                         -> Maybe (LEdge DGLinkLab, [LEdge DGLinkLab])
compositionForOneEdgeAux _ [] = Nothing
compositionForOneEdgeAux edge@(src,tgt,labl) (path:paths)
  | cons <= pathCons = if cons == Mono
                        then handleConservativityMono newEdge path
                         else Just (newEdge,path)
  | otherwise = compositionForOneEdgeAux edge paths
  where
    cons = getConservativity edge
    pathCons = getConservativityOfPath path
    newEdge = (src, tgt, labl
      { dgl_type = setProof (Proven (Composition path)
          $ foldl addEdgeId emptyProofBasis $ map getEdgeId path)
          $ dgl_type labl
      , dgl_origin = DGLinkProof
      , dgl_id = defaultEdgeId })

{- | checks if the morphism of the given path is transportable. This
is necessary for the composition of a path, if its conservativity is
Mono.  This method is used by compositionForOneEdgeAux to check, if a
composition in case of conservativity Mono is possible. -}
handleConservativityMono :: LEdge DGLinkLab -> [LEdge DGLinkLab]
                         -> Maybe (LEdge DGLinkLab, [LEdge DGLinkLab])
handleConservativityMono newEdge path =
  case calculateMorphismOfPath path of
    Nothing -> Nothing
    Just morph -> if isTransportable morph then Just (newEdge,path)
                   else Nothing
