{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

hide theorem shift proof in development graphs.
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

module Proofs.HideTheoremShift (hideTheoremShift) where

import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Data.Graph.Inductive.Graph
import Proofs.EdgeUtils
import Proofs.StatusUtils
import GUI.Utils

-- ----------------------------------------------
-- hide theorem shift
-- ----------------------------------------------

hideTheoremShift :: Bool -> ProofStatus -> IO ProofStatus
hideTheoremShift isAutomatic proofStatus@(ln,_,_) = do
  let dgraph = lookupDGraph ln proofStatus
      hidingThmEdges = filter isUnprovenHidingThm (labEdges dgraph)
  result <- hideTheoremShiftAux dgraph ([],[]) hidingThmEdges isAutomatic
  let nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus
          = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus


{- auxiliary method for hideTheoremShift -}
hideTheoremShiftAux :: DGraph -> ([DGRule],[DGChange])
                    -> [LEdge DGLinkLab] -> Bool 
                    -> IO (DGraph,([DGRule],[DGChange]))
hideTheoremShiftAux dgraph historyElement [] _ =
  return (dgraph, historyElement)
hideTheoremShiftAux dgraph (rules,changes) (ledge:list) isAutomatic = 
  do proofBasis <- findProofBasisForHideTheoremShift dgraph ledge isAutomatic
     if (null proofBasis)
      then hideTheoremShiftAux dgraph (rules,changes) list isAutomatic
       else do
         let newEdge = makeProvenHidingThmEdge proofBasis ledge
             auxDGraph = insEdge newEdge (delLEdge ledge dgraph)
             auxChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)
             (newDGraph,newChanges) = 
                 insertNewEdges auxDGraph auxChanges proofBasis
             newRules = (HideTheoremShift ledge):rules
         hideTheoremShiftAux newDGraph (newRules,newChanges) list isAutomatic

{- inserts the given edges into the development graph and adds a corresponding entry to the changes -}
insertNewEdges :: DGraph -> [DGChange] -> [LEdge DGLinkLab] -> (DGraph,[DGChange])
insertNewEdges dgraph changes [] = (dgraph,changes)
insertNewEdges dgraph changes (edge:list) =
  if isDuplicate edge dgraph changes then insertNewEdges dgraph changes list
   else insertNewEdges (insEdge edge dgraph) ((InsertEdge edge):changes) list


{- creates a new proven HidingThm edge from the given HidingThm edge using the edge list as the proofBasis -}
makeProvenHidingThmEdge :: [LEdge DGLinkLab] -> LEdge DGLinkLab -> LEdge DGLinkLab
makeProvenHidingThmEdge proofBasisEdges ledge@(src,tgt,edgeLab) =
  (src,
   tgt,
   DGLink {dgl_morphism = morphism,
           dgl_type = (HidingThm hidingMorphism 
                       (Proven (HideTheoremShift ledge) proofBasisEdges)),
           dgl_origin = DGProof}
  )
  where
    morphism = dgl_morphism edgeLab      
    (HidingThm hidingMorphism _) = (dgl_type edgeLab)


{- selects a proof basis for 'hide theorem shift' if there is one-}
findProofBasisForHideTheoremShift :: DGraph -> LEdge DGLinkLab -> Bool
                          -> IO [LEdge DGLinkLab]
findProofBasisForHideTheoremShift dgraph (ledge@(src,tgt,edgelab)) isAutomatic=
  if (null pathPairsFilteredByConservativity) then return []
   else 
     do pb <- hideTheoremShift_selectProofBasis dgraph 
                         pathPairsFilteredByConservativity isAutomatic
        case pb of
          Nothing -> return []
          Just proofBasis -> do let fstPath = fst proofBasis
                                    sndPath = snd proofBasis
                                return [createEdgeForPath fstPath, 
                                        createEdgeForPath sndPath]

   where
    pathsFromSrc = getAllPathsOfTypeFrom dgraph src (ledge /=)
    pathsFromTgt = getAllPathsOfTypeFrom dgraph tgt (ledge /=)
    possiblePathPairs = selectPathPairs pathsFromSrc pathsFromTgt
    (HidingThm hidingMorphism _) = (dgl_type edgelab)
    morphism = dgl_morphism edgelab
    pathPairsFilteredByMorphism 
        = filterPairsByResultingMorphisms possiblePathPairs
          hidingMorphism morphism
    pathPairsFilteredByConservativity
        = filterPairsByConservativityOfSecondPath pathPairsFilteredByMorphism


{- removes all pairs from the given list whose second path does not have a 
   conservativity greater than or equal to Cons -}
filterPairsByConservativityOfSecondPath :: 
    [([LEdge DGLinkLab],[LEdge DGLinkLab])] 
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


{- selects a proofBasis (i.e. a path tuple) from the list of possible ones:
   If there is exaclty one proofBasis in the list, this is returned.
   If there are more than one and the method is called in automatic mode Nothing is returned. In non-automatic mode the user is asked to select a proofBasis via listBox. -}
hideTheoremShift_selectProofBasis :: 
    DGraph -> [([LEdge DGLinkLab], [LEdge DGLinkLab])] -> Bool
                 -> IO (Maybe ([LEdge DGLinkLab], [LEdge DGLinkLab]))
hideTheoremShift_selectProofBasis _ (basis:[]) _ = return (Just basis)
hideTheoremShift_selectProofBasis dgraph basisList isAutomatic =
  case isAutomatic of
    True -> return Nothing
    False -> do sel <- listBox 
                       "Choose a path tuple as the proof basis"
                       (map (prettyPrintPathTuple dgraph) basisList)
                i <- case sel of
                       Just j -> return j
                       _ -> error ("Proofs.Proofs: " ++
                                   "selection of proof basis failed")
                return (Just (basisList!!i))


{- returns a string representation of the given paths:
   for each path a tuple of the names of its nodes is shown, the two are combined by an 'and' -}
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
   getDGNodeName $ lab' $ context dgraph src


{- returns the name of the target node of the given edge-}
prettyPrintTargetNode :: DGraph -> LEdge DGLinkLab -> String
prettyPrintTargetNode dgraph (_,tgt,_) =
   getDGNodeName $ lab' $ context dgraph tgt


{- creates a unproven global thm edge for the given path, i.e. with the same source and target nodes and the same morphism as the path -}
createEdgeForPath :: [LEdge DGLinkLab] -> LEdge DGLinkLab
createEdgeForPath path =
  case (calculateMorphismOfPath path) of
    Just morphism -> (getSourceNode (head path),
                      getTargetNode (last path),
                      DGLink {dgl_morphism = morphism,
                              dgl_type = (GlobalThm LeftOpen None
                                          LeftOpen),
                              dgl_origin = DGProof}
                     )    
    Nothing -> error "createEdgeForPath"


{- returns a list of path pairs, as shorthand the pairs are not returned as path-path tuples but as path-<list of path> tuples. Every path in the list is a pair of the single path.
The path pairs are selected by having the same target node. -}
selectPathPairs :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
                -> [([LEdge DGLinkLab],[[LEdge DGLinkLab]])]
selectPathPairs [] _ = []
selectPathPairs _ [] = []
selectPathPairs paths1 paths2 =
  [(p1,  [p2| p2 <- paths2, haveSameTgt (last p1) (last p2) ] )| p1 <- paths1]
  
  where
    haveSameTgt :: LEdge DGLinkLab -> LEdge DGLinkLab -> Bool
    haveSameTgt (_,tgt1,_) (_,tgt2,_) = tgt1 == tgt2

{- returns a list of path pairs by keeping those pairs, whose first path composed with the first given morphism and whose second path composed with the second given morphism result in the same morphism, and droping all other pairs.-}
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
    (Just m1, Just m2) -> resultToMaybe $ compHomInclusion m1 m2 
    _ -> Nothing

{- returns the Conservativity if the given edge has one,
   otherwise an error is raised -}
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm _ cons _) -> cons
    (GlobalThm _ cons _) -> cons
    _ -> None
