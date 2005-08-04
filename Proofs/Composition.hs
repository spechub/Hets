module Proofs.Composition (composition) where

import Proofs.EdgeUtils
import Proofs.Proofs
import Proofs.StatusUtils
import Static.DevGraph
import Data.Graph.Inductive.Graph

composition :: ProofStatus -> IO ProofStatus
composition proofStatus@(libname,libEnv,_) = do
  let dgraph = lookupDGraph libname proofStatus
      globalThmEdges = filter isGlobalThm (labEdges dgraph)
      (newDGraph, newHistoryElem) = compositionAux dgraph globalThmEdges ([],[])
      newProofStatus = mkResultProofStatus proofStatus newDGraph newHistoryElem
  return newProofStatus


compositionAux :: DGraph -> [LEdge DGLinkLab] -> ([DGRule],[DGChange]) -> (DGraph, ([DGRule],[DGChange]))
compositionAux dgraph [] historyElem = (dgraph,historyElem)
compositionAux dgraph (edge:edges) (rules,changes) =
  case compositionForOneEdge dgraph edge of
    Nothing -> compositionAux dgraph edges (rules,changes)
    Just (newEdge,proofBasis) ->
	compositionAux (insEdge newEdge (delLEdge edge dgraph))
		       edges
		       ((Composition proofBasis):rules,
			(InsertEdge newEdge):((DeleteEdge edge):changes))


compositionForOneEdge :: DGraph -> LEdge DGLinkLab -> Maybe (LEdge DGLinkLab,[LEdge DGLinkLab])
compositionForOneEdge dgraph edge@(src,tgt,lab) =
  compositionForOneEdgeAux edge pathsOfMorphism

  where
    globThmPaths = getAllPathsOfTypeBetween dgraph isGlobalThm src tgt
    pathsOfMorphism = filterPathsByMorphism (dgl_morphism lab) globThmPaths


compositionForOneEdgeAux :: LEdge DGLinkLab -> [[LEdge DGLinkLab]] -> Maybe (LEdge DGLinkLab,[LEdge DGLinkLab])
compositionForOneEdgeAux _ [] = Nothing
compositionForOneEdgeAux edge@(src,tgt,lab) (path:paths)
  | cons <= pathCons = Just (newEdge,path)
  | otherwise = compositionForOneEdgeAux edge paths

  where
    cons = getConservativity edge
    pathCons = minimum [getConservativity e | e <- path]
    consStatus = getConservativityStatus edge
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = dgl_morphism lab,
		       dgl_type = (GlobalThm (Proven (Composition path) (map getEdgeLabel path))) cons consStatus,
		       dgl_origin = DGProof}
	      )


getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity (_,_,lab) =
  case dgl_type lab of
    LocalThm _ cons _ -> cons
    GlobalThm _ cons _ -> cons


getConservativityStatus :: LEdge DGLinkLab -> ThmLinkStatus
getConservativityStatus (_,_,lab) =
  case dgl_type lab of
    LocalThm _ _ consStatus -> consStatus
    GlobalThm _ _ consStatus -> consStatus


getEdgeLabel :: LEdge DGLinkLab -> DGLinkLab
getEdgeLabel (_,_,label) = label