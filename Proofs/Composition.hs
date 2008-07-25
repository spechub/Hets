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

import Logic.Grothendieck
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Syntax.AS_Library
import Static.DevGraph
import qualified Common.Lib.Graph as Tree
import Data.Graph.Inductive.Graph
import Data.List

compositionCreatingEdgesFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv
                                 -> LibEnv
compositionCreatingEdgesFromList libname ls proofStatus =
      let dgraph = lookupDGraph libname proofStatus
          pathsToCompose = filter ((> 1) . length) $
              getAllPathsOfTypeFromGoalList dgraph isGlobalThm ls
          (newDGraph, newHistoryElem)
                 = compositionCreatingEdgesAux dgraph pathsToCompose ([], [])
      in mkResultProofStatus libname proofStatus newDGraph newHistoryElem

{- | creates new edges by composing all paths of global theorem edges
   in the current development graph. These new edges are proven global
   theorems with the morphism and the conservativity of the corresponding
   path. If a new edge is the proven version of a previsously existing
   edge, that edge is deleted. -}
compositionCreatingEdges :: LIB_NAME -> LibEnv -> LibEnv
compositionCreatingEdges libname proofStatus =
    let dgraph = lookupDGraph libname proofStatus
        allEdges = labEdgesDG dgraph
    in compositionCreatingEdgesFromList libname allEdges proofStatus

{- auxiliary method for compositionCreatingEdges -}
compositionCreatingEdgesAux :: DGraph -> [[LEdge DGLinkLab]]
                          -> ([DGRule],[DGChange])
                          -> (DGraph,([DGRule],[DGChange]))
compositionCreatingEdgesAux dgraph [] historyElem = (dgraph,historyElem)
compositionCreatingEdgesAux dgraph (path:paths) (rules,changes) =
 case calculateMorphismOfPath path of
   Nothing -> compositionCreatingEdgesAux dgraph paths (rules,changes)
   Just _ -> compositionCreatingEdgesAux newDGraph2 paths
             (Composition path : rules,
              changes ++ newChanges ++ newChanges2)
  where
    (src, _, _) = head path
    (_, tgt, _) = last path
    Just morph = calculateMorphismOfPath path
    cons = case getConservativityOfPath path of
             Mono -> if isTransportable morph then Mono else Cons
             c -> c
    consStatus = LeftOpen
    newEdge = (src,
               tgt,
               DGLink {dgl_morphism = morph,
                       dgl_type = (GlobalThm (Proven (Composition path)
                                    $ foldl addEdgeId emptyProofBasis
                                    $ map getEdgeId path))
                       cons consStatus,
                       dgl_origin = DGLinkProof,
                       dgl_id = defaultEdgeId}
              )
    (newDGraph, newChanges) = insertDGLEdge newEdge dgraph
    (newDGraph2, newChanges2) = deleteRedundantEdges newDGraph newEdge


{- | this method is used by compositionCreatingEdgesAux.  It selects
all unproven global theorem edges in the given development graph that
have the same source, target, morphism and conservativity as the given
one. It then deletes them from the given graph and adds a
corresponding change -}
deleteRedundantEdges :: DGraph -> LEdge DGLinkLab -> (DGraph, [DGChange])
deleteRedundantEdges dgraph (src, tgt, labl) = let
    redundantEdges =
      [ (src, tgt, l) | l <- Tree.getLEdges src tgt $ dgBody dgraph
      , isUnprovenGlobalThm $ dgl_type l
      , dgl_morphism l == dgl_morphism labl
      , haveSameCons l labl ]
    haveSameCons :: DGLinkLab -> DGLinkLab -> Bool
    haveSameCons lab1 lab2 = case (dgl_type lab1, dgl_type lab2) of
          (GlobalThm LeftOpen cons1 status1,
           GlobalThm _ cons2 status2) ->
             cons1 == cons2 &&
             isProvenThmLinkStatus status1 == isProvenThmLinkStatus status2
          _ -> False
    (newGraph, changes) =
      mapAccumL deleteRedundantEdgesAux dgraph redundantEdges
   in (newGraph, concat changes)

{- auxiliary method for deleteRedundantEdgesAux -}
deleteRedundantEdgesAux :: DGraph -> LEdge DGLinkLab -> (DGraph, [DGChange])
deleteRedundantEdgesAux dgraph edge =
    updateWithOneChange (DeleteEdge edge) dgraph

-- | composition without creating new new edges
compositionFromList :: LIB_NAME -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
compositionFromList libname glbThmEdge proofStatus = let
    dgraph = lookupDGraph libname proofStatus
    (newDGraph, newHistoryElems) = mapAccumL compositionAux dgraph
      $ filter (liftE isGlobalThm) $ glbThmEdge
  in mkResultProofStatus libname proofStatus newDGraph
     (concatMap fst newHistoryElems, concatMap snd newHistoryElems)

{- | gets all unproven global theorem edges in the current development graph
   and checks, if they are a composition of a global theorem path. If so,
   the edge is proven, with the corresponding path as its proof basis.
   If there is more than one path, the first of them is arbitrarily taken. -}
composition :: LIB_NAME -> LibEnv -> LibEnv
composition libname proofStatus =
  let dgraph = lookupDGraph libname proofStatus
      globalThmEdges = labEdgesDG dgraph
  in compositionFromList libname globalThmEdges proofStatus

{- | auxiliary method for composition -}
compositionAux :: DGraph -> LEdge DGLinkLab -> (DGraph, ([DGRule], [DGChange]))
compositionAux dgraph edge =
  case compositionForOneEdge dgraph edge of
    Nothing -> (dgraph, emptyHistory)
    Just (newEdge, proofbasis) -> let
        (newDGraph, newChanges) =
            updateWithChanges [DeleteEdge edge, InsertEdge newEdge] dgraph
        in (newDGraph, ([Composition proofbasis], newChanges))

{- | checks for the given edges, if there is a path in the given
development graph that it is a composition of. If so, it is replaced
by a proven version with the path as its proof basis.  The method
returns Nothing if there is no such path or else the new edge and the
path. -}
compositionForOneEdge :: DGraph -> LEdge DGLinkLab
                      -> Maybe (LEdge DGLinkLab,[LEdge DGLinkLab])
compositionForOneEdge dgraph edge@(src,tgt,labl) =
  compositionForOneEdgeAux edge [path | path <- pathsOfMorphism,
                                 noPath edge path]
  where
    globThmPaths = getAllPathsOfTypeBetween dgraph isGlobalThm src tgt
    pathsOfMorphism = filterPathsByMorphism (dgl_morphism labl) globThmPaths

{- auxiliary method for compositionForOneEdge -}
compositionForOneEdgeAux :: LEdge DGLinkLab -> [[LEdge DGLinkLab]]
                         -> Maybe (LEdge DGLinkLab,[LEdge DGLinkLab])
compositionForOneEdgeAux _ [] = Nothing
compositionForOneEdgeAux edge@(src,tgt,labl) (path:paths)
  | cons <= pathCons = if cons == Mono
                        then handleConservativityMono newEdge path
                         else Just (newEdge,path)
  | otherwise = compositionForOneEdgeAux edge paths
  where
    cons = getConservativity edge
    pathCons = getConservativityOfPath path
    consStatus = getConservativityStatus edge
    newEdge = (src,
               tgt,
               DGLink {dgl_morphism = dgl_morphism labl,
                       dgl_type = GlobalThm (Proven (Composition path)
                                   $ foldl addEdgeId emptyProofBasis
                                   $ map getEdgeId path) cons consStatus,
                       dgl_origin = DGLinkProof,
                       dgl_id = defaultEdgeId}
              )

{- | checks if the morphism of the given path is transportable. This
is necessary for the composition of a path, if its conservativity is
Mono.  This method is used by compositionForOneEdgeAux to check, if a
composition in case of conservativity Mono is possible. -}
handleConservativityMono :: LEdge DGLinkLab -> [LEdge DGLinkLab]
                         -> Maybe (LEdge DGLinkLab,[LEdge DGLinkLab])
handleConservativityMono newEdge path =
  case calculateMorphismOfPath path of
    Nothing -> Nothing
    Just morph -> if isTransportable morph then Just (newEdge,path)
                   else Nothing

{- | returns the conservativity of the given edge -}
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_,_,labl) =
  case dgl_type labl of
    LocalThm _ cons _ -> cons
    GlobalThm _ cons _ -> cons
    _ -> error "getConservativity"

{- | returns the conservativity of the given path -}
getConservativityOfPath :: [LEdge DGLinkLab] -> Conservativity
getConservativityOfPath path = minimum [getConservativity e | e <- path]

{- | returns the conservativity status of the given edge -}
getConservativityStatus :: LEdge DGLinkLab -> ThmLinkStatus
getConservativityStatus (_,_,labl) =
  case dgl_type labl of
    LocalThm _ _ consStatus -> consStatus
    GlobalThm _ _ consStatus -> consStatus
    _ -> error "getConservativityStatus"
