{- |
Module      :  $Header$
Description :  hide theorem shift proof rule for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

hide theorem shift proof rule for development graphs
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.
-}

module Proofs.HideTheoremShift
    ( interactiveHideTheoremShift
    , automaticHideTheoremShift
    , automaticHideTheoremShiftFromList
    ) where

import Proofs.EdgeUtils
import Comorphisms.LogicGraph
import GUI.Utils

import Logic.Grothendieck
import Static.DevGraph

import Common.LibName
import Common.Result

import Control.Monad.Identity
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import Data.List

type ListSelector m a = [a] -> m (Maybe a)
type PathTuple = ([LEdge DGLinkLab], [LEdge DGLinkLab])
type ProofBaseSelector m = DGraph -> ListSelector m PathTuple

hideThmShiftRule :: LEdge DGLinkLab -> DGRule
hideThmShiftRule = DGRuleWithEdge "HideTheoremShift"

interactiveHideTheoremShift :: LIB_NAME -> LibEnv -> IO LibEnv
interactiveHideTheoremShift =
    hideTheoremShift hideTheoremShift_selectProofBase

automaticHideTheoremShift :: LIB_NAME -> LibEnv -> LibEnv
automaticHideTheoremShift ln libEnv =
    let dgraph = lookupDGraph ln libEnv
        ls = filter (liftE isUnprovenHidingThm) $ labEdgesDG dgraph
    in automaticHideTheoremShiftFromList ln ls libEnv

automaticHideTheoremShiftFromList :: LIB_NAME -> [LEdge DGLinkLab]-> LibEnv
                                  -> LibEnv
automaticHideTheoremShiftFromList ln ls = runIdentity. hideTheoremShiftFromList
      (const $ \ l -> return $ case l of
                      [a] -> Just a -- maybe take the first one always ?
                      _   -> Nothing) ln ls

hideTheoremShiftFromList :: Monad m => ProofBaseSelector m -> LIB_NAME
                     -> [LEdge DGLinkLab] -> LibEnv  -> m LibEnv
hideTheoremShiftFromList proofBaseSel ln hidingThmEdges proofStatus = do
    let dgraph = lookupDGraph ln proofStatus
        finalHidingThmEdges = filter (liftE isUnprovenHidingThm) hidingThmEdges
    nextDGraph <- foldM
       (hideTheoremShiftAux proofBaseSel) dgraph finalHidingThmEdges
    return $ Map.insert ln nextDGraph proofStatus

hideTheoremShift :: Monad m => ProofBaseSelector m -> LIB_NAME
                 -> LibEnv -> m LibEnv
hideTheoremShift proofBaseSel ln proofStatus =
    let dgraph = lookupDGraph ln proofStatus
        hidingThmEdges = labEdgesDG dgraph
    in hideTheoremShiftFromList proofBaseSel ln hidingThmEdges proofStatus

{- | auxiliary method for hideTheoremShift.
     it contains three steps: inserting of the proof basis, deleting of the
     current edge and inserting of the new proven edge.
-}
hideTheoremShiftAux :: Monad m => ProofBaseSelector m -> DGraph
                    -> LEdge DGLinkLab -> m DGraph
hideTheoremShiftAux proofBaseSel dgraph ledge =
  do proofbasis <- findProofBaseForHideTheoremShift dgraph ledge proofBaseSel
     return $ if null proofbasis
      then dgraph
       else
         let (auxDGraph, finalProofBasis) =
                 foldl insertNewEdges (dgraph, emptyProofBasis) proofbasis
             newEdge = makeProvenHidingThmEdge finalProofBasis ledge
             newDGraph2 = changeDGH auxDGraph $ DeleteEdge ledge
             newDGraph = insertDGLEdge newEdge newDGraph2
             newRules = hideThmShiftRule ledge
         in groupHistory dgraph newRules newDGraph

{- | inserts the given edges into the development graph and adds a
     corresponding entry to the changes, while getting the proofbasis.
     Notice that EdgeId is enough to represent an edge and can therefore
     be used as proof basis.
-}
insertNewEdges :: (DGraph, ProofBasis) -> LEdge DGLinkLab
               -> (DGraph, ProofBasis)
insertNewEdges (dgraph, proofbasis) edge =
  case tryToGetEdge edge dgraph of
       Just e -> (dgraph, addEdgeId proofbasis $ getEdgeId e)
       Nothing -> let
                  tempDGraph = changeDGH dgraph $ InsertEdge edge
                  -- checks if the edge is actually inserted
                  tempProofBasis = case getLastChange tempDGraph of
                    InsertEdge tempE ->
                        addEdgeId proofbasis $ getEdgeId tempE
                    _ -> error ("Proofs"++
                                ".HideTheoremShift"++
                                ".insertNewEdges")
                  in (tempDGraph, tempProofBasis)

{- | creates a new proven HidingThm edge from the given
     HidingThm edge using the edge list as the proofbasis
-}
makeProvenHidingThmEdge :: ProofBasis -> LEdge DGLinkLab -> LEdge DGLinkLab
makeProvenHidingThmEdge proofBasisEdges ledge@(src,tgt,edgeLab) =
  let HidingThm hidingMorphism _ = dgl_type edgeLab
  in (src, tgt, edgeLab
       { dgl_type = HidingThm hidingMorphism
           $ Proven (hideThmShiftRule ledge) proofBasisEdges
       , dgl_origin = DGLinkProof })

{- | selects a proof basis for 'hide theorem shift' if there is one
-}
findProofBaseForHideTheoremShift :: Monad m => DGraph -> LEdge DGLinkLab
                                 -> ProofBaseSelector m -> m [LEdge DGLinkLab]
findProofBaseForHideTheoremShift dgraph (ledge@(src,tgt, lb)) proofBaseSel = do
  let dgraph2 = delLEdgeDG ledge dgraph
      pathsFromSrc = getAllPathsOfTypeFrom dgraph2 src
      pathsFromTgt = getAllPathsOfTypeFrom dgraph2 tgt
      possiblePathPairs = selectPathPairs pathsFromSrc pathsFromTgt
      HidingThm hidingMorphism _ = dgl_type lb
      morphism = dgl_morphism lb
      pathPairsFilteredByMorphism
        = filterPairsByResultingMorphisms possiblePathPairs
          hidingMorphism morphism
      pathPairsFilteredByConservativity
        = filterPairsByConservativityOfSecondPath pathPairsFilteredByMorphism
      -- advoiding duplicate to be selected proofbasis.
      pathPairsFilteredByProveStatus
        = filterPairsByGlobalProveStatus pathPairsFilteredByConservativity
  pb <- proofBaseSel dgraph pathPairsFilteredByProveStatus
  return $ case pb of
          Nothing -> []
          Just (fstPath, sndPath) -> map createEdgeForPath [fstPath, sndPath]

{- | advoiding duplicate to be selected proofbasis.
-}
filterPairsByGlobalProveStatus :: [([LEdge DGLinkLab], [LEdge DGLinkLab])]
                               -> [([LEdge DGLinkLab], [LEdge DGLinkLab])]
filterPairsByGlobalProveStatus = filter bothAreProven where
  bothAreProven (pb1, pb2) = allAreProven pb1 && allAreProven pb2
  allAreProven = all $ liftE (\ l -> isProven l && isGlobalEdge l)

{- removes all pairs from the given list whose second path does not have a
   conservativity greater than or equal to Cons -}
filterPairsByConservativityOfSecondPath
    :: [([LEdge DGLinkLab],[LEdge DGLinkLab])]
    -> [([LEdge DGLinkLab],[LEdge DGLinkLab])]
filterPairsByConservativityOfSecondPath [] = []
filterPairsByConservativityOfSecondPath (([],_):list) =
  filterPairsByConservativityOfSecondPath list
filterPairsByConservativityOfSecondPath ((_,[]):list) =
  filterPairsByConservativityOfSecondPath list
filterPairsByConservativityOfSecondPath (pair:list) =
  if (and [cons >= Cons | cons <- map getConservativity (snd pair)])
   then pair:(filterPairsByConservativityOfSecondPath list)
    else filterPairsByConservativityOfSecondPath list

{- | selects a proofBasis (i.e. a path tuple) from the list of possible ones:
     If there is exaclty one proofBasis in the list, this is returned.
     If there are more than one and the method is called in automatic mode
     Nothing is returned.
     In non-automatic mode the user is asked to select a proofBasis via
     listBox, then the selected one will be returned.
-}
hideTheoremShift_selectProofBase
    :: DGraph -> [([LEdge DGLinkLab], [LEdge DGLinkLab])]
    -> IO (Maybe ([LEdge DGLinkLab], [LEdge DGLinkLab]))
hideTheoremShift_selectProofBase dgraph basisList =
  case basisList of
    [] -> return Nothing
    [basis] -> return $ Just basis
    _ -> do
         sel <- listBox
                       "Choose a path tuple as the proof basis"
                       (map (prettyPrintPathTuple dgraph) basisList)
         case sel of
             Just j -> return $ Just (basisList !! j)
             _ -> return Nothing

{- returns a string representation of the given paths: for each path a
   tuple of the names of its nodes is shown, the two are combined by
   an \'and\' -}
prettyPrintPathTuple :: DGraph -> ([LEdge DGLinkLab],[LEdge DGLinkLab])
                     -> String
prettyPrintPathTuple dgraph (p1,p2) =
  (prettyPrintPath dgraph p1) ++ " and " ++ (prettyPrintPath dgraph p2)

{- returns the names of the nodes of the path, separated by commas-}
prettyPrintNodesOfPath :: DGraph -> [LEdge DGLinkLab] -> String
prettyPrintNodesOfPath _ [] = ""
prettyPrintNodesOfPath dgraph (edge:path) =
  (prettyPrintSourceNode dgraph edge) ++ ", "
  ++ (prettyPrintNodesOfPath dgraph path)
  ++ end
  where
    end = case path of
            [] -> prettyPrintTargetNode dgraph edge
            _ -> ""

{- returns a string reprentation of the path: showing a tuple of its nodes-}
prettyPrintPath :: DGraph -> [LEdge DGLinkLab] -> String
prettyPrintPath _ [] = "<empty path>"
prettyPrintPath dgraph path =
  "(" ++ (prettyPrintNodesOfPath dgraph path) ++ ")"

{- returns the name of the source node of the given edge-}
prettyPrintSourceNode :: DGraph -> LEdge DGLinkLab -> String
prettyPrintSourceNode dgraph (src,_,_) =
   getDGNodeName $ labDG dgraph src

{- returns the name of the target node of the given edge-}
prettyPrintTargetNode :: DGraph -> LEdge DGLinkLab -> String
prettyPrintTargetNode dgraph (_,tgt,_) =
   getDGNodeName $ labDG dgraph tgt

{- creates a unproven global thm edge for the given path, i.e. with
the same source and target nodes and the same morphism as the path -}
createEdgeForPath :: [LEdge DGLinkLab] -> LEdge DGLinkLab
createEdgeForPath path =
  case (calculateMorphismOfPath path, path) of
    (Just morphism, (s, _, _) : _) ->
        let (_, t, _) = last path
        in (s, t,
                      DGLink { dgl_morphism = morphism
                             , dgl_type = (GlobalThm LeftOpen None LeftOpen)
                             , dgl_origin = DGLinkProof
                             , dgl_id = defaultEdgeId
                             }
                     )
    _ -> error "createEdgeForPath"

{- returns a list of path pairs, as shorthand the pairs are not
returned as path-path tuples but as path-<list of path> tuples. Every
path in the list is a pair of the single path.  The path pairs are
selected by having the same target node. -}
selectPathPairs :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
                -> [([LEdge DGLinkLab],[[LEdge DGLinkLab]])]
selectPathPairs [] _ = []
selectPathPairs _ [] = []
selectPathPairs paths1 paths2 =
  [(p1,  [p2| p2 <- paths2, haveSameTgt (last p1) (last p2) ] )| p1 <- paths1]

  where
    haveSameTgt :: LEdge DGLinkLab -> LEdge DGLinkLab -> Bool
    haveSameTgt (_,tgt1,_) (_,tgt2,_) = tgt1 == tgt2

{- returns a list of path pairs by keeping those pairs, whose first
path composed with the first given morphism and whose second path
composed with the second given morphism result in the same morphism,
and dropping all other pairs.-}
filterPairsByResultingMorphisms :: [([LEdge DGLinkLab],[[LEdge DGLinkLab]])]
                                -> GMorphism -> GMorphism
                                -> [([LEdge DGLinkLab],[LEdge DGLinkLab])]
filterPairsByResultingMorphisms [] _ _ = []
filterPairsByResultingMorphisms (pair:pairs) morph1 morph2 =
  [((fst pair),path)| path <- suitingPaths]
          ++ (filterPairsByResultingMorphisms pairs morph1 morph2)

  where
    compMorph1
        = compMaybeMorphisms (Just morph1) (calculateMorphismOfPath (fst pair))
    suitingPaths :: [[LEdge DGLinkLab]]
    suitingPaths = if (compMorph1 /= Nothing) then
                      [path |path <- (snd pair),
                       (compMaybeMorphisms (Just morph2)
                                           (calculateMorphismOfPath path))
                       == compMorph1]
                    else []

{- if the given maybe morphisms are both not Nothing,
   this method composes their GMorphisms -
   returns Nothing otherwise -}
compMaybeMorphisms :: Maybe GMorphism -> Maybe GMorphism -> Maybe GMorphism
compMaybeMorphisms morph1 morph2 =
  case (morph1, morph2) of
    (Just m1, Just m2) -> resultToMaybe $ compInclusion logicGraph m1 m2
       -- This should be compInclusion, but this would need the logic graph
    _ -> Nothing

{- returns the Conservativity if the given edge has one,
   otherwise an error is raised -}
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm _ cons _) -> cons
    (GlobalThm _ cons _) -> cons
    _ -> None
