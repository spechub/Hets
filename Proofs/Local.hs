{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

local proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{- 

Order of rule application: try to use local links induced by %implies 
for subsumption proofs (such that the %implied formulas need not be
re-proved)

-}

module Proofs.Local (locSubsume, locDecomp) where

import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Data.Graph.Inductive.Graph
import Proofs.Proofs
import Proofs.EdgeUtils
import Proofs.StatusUtils
import Syntax.AS_Library

-- --------------------
-- local decomposition
-- --------------------

{- a merge of the rules local subsumption, local decomposition I and 
   local decomposition II -}
-- applies this merge of rules to all unproven localThm edges if possible
locDecomp ::  ProofStatus -> IO ProofStatus
locDecomp proofStatus@(ln,libEnv,_) = do
  let dgraph = lookupDGraph ln proofStatus
      localThmEdges = filter isUnprovenLocalThm (labEdges dgraph)
      result = locDecompAux libEnv ln dgraph ([],[]) localThmEdges
      nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus 
	  = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> LIB_NAME -> DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locDecompAux _ _ dgraph historyElement [] = (dgraph, historyElement)
locDecompAux libEnv ln dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if (null proofBasis && not (isIdentityEdge ledge libEnv dgraph))
     then
       locDecompAux libEnv ln dgraph (rules,changes) list
     else
       if isDuplicate newEdge dgraph changes
          then locDecompAux libEnv ln auxGraph 
                 (newRules,(DeleteEdge ledge):changes) list
       else locDecompAux libEnv ln newGraph (newRules,newChanges) list

  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    th = computeLocalTheory libEnv (ln, src)
    pathsWithoutEdgeItself = [path|path <- allPaths, notElem ledge path]
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
    proofBasis = selectProofBasis edgeLab filteredPaths
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven (LocDecomp ledge) proofBasis)
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (LocDecomp ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)


{- removes all paths from the given list of paths whose morphism does not translate the given sentence list to the same resulting sentence list as the given morphism-}
filterByTranslation :: Maybe G_theory -> GMorphism -> [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterByTranslation maybeTh morphism paths =
  case maybeTh of
    Just th -> [path| path <- paths, isSameTranslation th morphism path]
    Nothing -> []
--     isSameTranslation th morphism (calculateMorphismOfPath path)]

{- checks if the given morphism and the morphism of the given path translate the given sentence list to the same resulting sentence list -}
isSameTranslation :: G_theory -> GMorphism -> [LEdge DGLinkLab] -> Bool
isSameTranslation th morphism path =
  case calculateMorphismOfPath path of
      Just morphismOfPath -> 
         translateG_theory morphism th == translateG_theory morphismOfPath th
      Nothing -> False

-- ----------------------------------------------
-- local subsumption
-- ----------------------------------------------

-- applies local subsumption to all unproven local theorem edges
locSubsume :: ProofStatus -> IO ProofStatus
locSubsume proofStatus@(ln,libEnv,_) = do
  let dgraph = lookupDGraph ln proofStatus
      localThmEdges = filter isUnprovenLocalThm (labEdges dgraph)
      result = locSubsumeAux libEnv ln dgraph ([],[]) localThmEdges
      nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus
	  = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus

-- auxiliary method for locSubsume
locSubsumeAux :: LibEnv -> LIB_NAME -> DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locSubsumeAux _ _ dgraph historyElement [] = (dgraph, historyElement)
locSubsumeAux libEnv ln dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  case (getDGNode libEnv dgraph tgt, maybeThSrc) of
    (Just (target,_), Just thSrc) ->
      case (maybeResult (computeTheory libEnv ln dgraph target), maybeResult (translateG_theory morphism thSrc)) of
        (Just theoryTgt, Just (G_theory lidSrc _ sensSrc)) ->
          case maybeResult (coerceTheory lidSrc theoryTgt) of
            Nothing -> locSubsumeAux libEnv ln dgraph (rules,changes) list
	    Just (_,sentencesTgt) ->
              if (all (`elem` sentencesTgt) sensSrc) 
               then locSubsumeAux libEnv ln newGraph (newRules,newChanges) list
                else locSubsumeAux libEnv ln dgraph (rules,changes) list
        _ -> locSubsumeAux libEnv ln dgraph (rules,changes) list
    _ -> -- showDiags defaultHetcatsOpts (errSrc++errTgt)
		 locSubsumeAux libEnv ln dgraph (rules,changes) list

  where
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalTheory libEnv (ln, src)
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven (LocSubsumption ledge) [])
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (LocSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)


