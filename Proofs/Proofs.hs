{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
-}

{- 
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

todo:

Integrate stuff from Saarbrücken
Add proof status information

 what should be in proof status:

- proofs of thm links according to rules
- cons, def and mono annos, and their proofs


-}
module Proofs.Proofs where

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Static.DevGraph
import Common.Result
import Common.Lib.Graph
-- neu:
import Common.Lib.Set (fromList)
import qualified Common.Lib.Map as Map
import List(nub)
import Common.Id
import Common.AS_Annotation
import Syntax.AS_Library
import Syntax.Print_AS_Library 


{- proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}
type ProofStatus = (GlobalContext,[([DGRule],[DGChange])],DGraph)

data DGRule = 
   TheoremHideShift
 | HideTheoremShift
 | Borrowing
 | ConsShift
 | DefShift 
 | MonoShift
 | ConsComp
 | DefComp 
 | MonoComp
 | DefToMono
 | MonoToCons
 | FreeIsMono
 | MonoIsFree
 | Composition
 | GlobDecomp (LEdge DGLinkLab)  -- edge in the conclusion
 | LocDecomp (LEdge DGLinkLab)
 | GlobSubsumption (LEdge DGLinkLab)
 | LocalInference
 | BasicInference Edge BasicProof
 | BasicConsInference Edge BasicConsProof

data DGChange = InsertNode (LNode DGNodeLab)
              | DeleteNode Node 
              | InsertEdge (LEdge DGLinkLab)
              | DeleteEdge (LEdge DGLinkLab)

data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (Proof_status sentence proof_tree)
     |  Guessed
     |  Conjectured
     |  Handwritten

data BasicConsProof = BasicConsProof -- more detail to be added ...

{- todo: implement apply for GlobDecomp and Subsumption 
   the list of DGChage must be constructed in parallel to the
   new DGraph -}
applyRule :: DGRule -> DGraph -> Maybe ([DGChange],DGraph)
applyRule = error "Proofs.hs:applyRule"

-- ---------------------
-- global decomposition
-- ---------------------

{- apply rule GlobDecomp to all global theorem links in the current DG 
   current DG = DGm
   add to proof status the pair ([GlobDecomp e1,...,GlobDecomp en],DGm+1)
   where e1...en are the global theorem links in DGm
   DGm+1 results from DGm by application of GlobDecomp e1,...,GlobDecomp en -}



{- applies global decomposition to all unproven global theorem edges
   if possible -}
globDecomp :: ProofStatus -> ProofStatus
globDecomp proofStatus@(globalContext,history,dgraph) =
  (globalContext, ((newHistoryElem):history), newDgraph)

  where
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
    (newDgraph, newHistoryElem) = globDecompAux dgraph globalThmEdges ([],[])

{- auxiliary function for globDecomp (above)
   actual implementation -}
globDecompAux :: DGraph -> [LEdge DGLinkLab] -> ([DGRule],[DGChange])
	      -> (DGraph,([DGRule],[DGChange]))
globDecompAux dgraph [] historyElem = (dgraph, historyElem)
globDecompAux dgraph (edge:edges) historyElem =
  globDecompAux newDGraph edges newHistoryElem

  where
    (newDGraph, newChanges) = globDecompForOneEdge dgraph edge
    newHistoryElem = (((GlobDecomp edge):(fst historyElem)),
			(newChanges++(snd historyElem)))

-- applies global decomposition to a single edge
globDecompForOneEdge :: DGraph -> LEdge DGLinkLab -> (DGraph,[DGChange])
globDecompForOneEdge dgraph edge =
  globDecompForOneEdgeAux dgraph edge [] paths
  
  where
    pathsToSource = getAllLocGlobDefPathsTo dgraph (getSourceNode edge) []
    paths = [(node, path++(edge:[]))| (node,path) <- pathsToSource]

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange] ->
			   [(Node, [LEdge DGLinkLab])] -> (DGraph,[DGChange])
{- if the list of paths is empty from the beginning, nothing is done
   otherwise the unprovenThm edge is replaced by a proven one -}
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes [] = 
  if null changes then (dgraph, [])
   else ((insEdge provenEdge (delLEdge edge dgraph)),
	    ((DeleteEdge edge):((InsertEdge provenEdge):changes)))

  where
    (GlobalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    proofBasis = getLabelsOfInsertedEdges changes
    provenEdge = (source,
		  target,
		  DGLink {dgl_morphism = dgl_morphism edgeLab,
			  dgl_type = 
			    (GlobalThm (Proven proofBasis)
			     conservativity conservStatus),
			  dgl_origin = DGProof}
		  )
-- for each path an unproven localThm edge is inserted
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes
 ((node,path):list) =
  globDecompForOneEdgeAux newGraph edge newChanges list

  where
    morphism = case calculateMorphismOfPath path of
                 Just morph -> morph
                 Nothing ->
		   error "globDecomp: could not determine morphism of new edge"
    newEdge = (node,
	       target,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (LocalThm (Static.DevGraph.Open)
				   None (Static.DevGraph.Open)),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge dgraph
    newChanges = ((InsertEdge newEdge):changes)


-- -------------------
-- global subsumption
-- -------------------

-- applies global subsumption to all unproven global theorem edges if possible
globSubsume ::  ProofStatus -> ProofStatus
globSubsume proofStatus@(globalContext,history,dGraph) =
  (globalContext, nextHistoryElem:history, nextDGraph)

  where
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dGraph)
    result = globSubsumeAux dGraph ([],[]) globalThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

{- auxiliary function for globSubsume (above)
   the actual implementation -}
globSubsumeAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux dgraph historyElement [] = (dgraph, historyElement)
globSubsumeAux dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if not (null proofBasis) || isIdentityEdge ledge dgraph
   then
     globSubsumeAux (insEdge newEdge (delLEdge ledge dgraph)) (newRules,newChanges) list
   else 
     globSubsumeAux dgraph (rules,changes) list

  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllGlobPathsOfMorphismBetween dgraph morphism src tgt
    filteredPaths = [path| path <- allPaths, notElem ledge path]
    proofBasis = selectProofBasis edgeLab filteredPaths
    (GlobalThm _ conservativity conservStatus) = dgl_type edgeLab
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (GlobalThm (Proven proofBasis)
				   conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newRules = (GlobSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)

isIdentityEdge :: LEdge DGLinkLab -> DGraph -> Bool
isIdentityEdge (src,tgt,edgeLab) dgraph =
  if isDGRef nodeLab then undefined --isIdentityEdge ...
   else if src == tgt && (dgl_morphism edgeLab) == (ide Grothendieck (dgn_sign nodeLab)) then True else False

  where nodeLab = lab' (context src dgraph)


{- returns the DGLinkLab of the given LEdge -}
getLabelOfEdge :: (LEdge b) -> b
getLabelOfEdge (_,_,label) = label

-- --------------------
-- local decomposition
-- --------------------

{- a merge of the rules local subsumption, local decomposition I and 
   local decomposition II -}
-- applies this merge of rules to all unproven localThm edges if possible
locDecomp ::  ProofStatus -> ProofStatus
locDecomp proofStatus@(globalContext,history,dGraph) =
  (globalContext, nextHistoryElem:history, nextDGraph)

  where
    localThmEdges = filter isUnprovenLocalThm (labEdges dGraph)
    result = locDecompAux dGraph ([],[]) localThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locDecompAux dgraph historyElement [] = (dgraph, historyElement)
locDecompAux dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if null proofBasis
     then
       globSubsumeAux dgraph (rules,changes) list     
     else
       globSubsumeAux newGraph (newRules,newChanges) list


  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    sens = dgn_sens (getNodeLab src dgraph)
    pathsWithoutEdgeItself = [path|path <- allPaths, notElem ledge path]
    filteredPaths = filterByTranslation sens morphism pathsWithoutEdgeItself
    proofBasis = selectProofBasis edgeLab filteredPaths
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven proofBasis)
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (LocDecomp ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)


{- returns the DGNodeLab of the given node -}
getNodeLab :: Node -> DGraph -> DGNodeLab
getNodeLab node dgraph =
  case nodeLab of
-- wie bekomme ich mit dem libname den zugehoerigen dgraph??
  --  (DGRef _ _ _) -> getNodeLab (dgn_node nodeLab) (dgn_libname nodeLab)
    (DGNode _ _ _ _) -> nodeLab

    where nodeLab = lab' (context node dgraph)

{- removes all paths from the given list of paths whose morphism does not translate the given sentence list to the same resulting sentence list as the given morphism-}
filterByTranslation :: G_l_sentence_list -> GMorphism -> [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterByTranslation sens morphism paths =
  [path| path <- paths, isSameTranslation sens morphism path]
--     isSameTranslation sens morphism (calculateMorphismOfPath path)]

{- checks if the given morphism and the morphism of the given path translate the given sentence list to the same resulting sentence list -}
isSameTranslation :: G_l_sentence_list -> GMorphism -> [LEdge DGLinkLab] -> Bool
isSameTranslation sens morphism path =
  case calculateMorphismOfPath path of
      Just morphismOfPath -> isSameTranslationAux sens morphism morphismOfPath
      Nothing -> False

{- checks if the two given morphisms translate the given sentence list to the same resulting sentence list
if the calculation of one of the resulting sentence lists fails, False is returned -}
isSameTranslationAux :: G_l_sentence_list -> GMorphism -> GMorphism -> Bool
isSameTranslationAux sens mor1 mor2 =
  case maybeResult maybeSens1 of
    Nothing -> False
    Just sens1 ->
      case maybeResult maybeSens2 of
        Nothing -> False
        Just sens2 -> eq_G_l_sentence_set sens1 sens2
  where
    maybeSens1 = translateG_l_sentence_list mor1 sens
    maybeSens2 = translateG_l_sentence_list mor2 sens
-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------

{- returns a list of all proven global paths of the given morphism between
   the given source and target node-}
getAllGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
					  -> [[LEdge DGLinkLab]]
getAllGlobPathsOfMorphismBetween dgraph morphism src tgt = 
  filterPathsByMorphism morphism allPaths

  where 
      allPaths = getAllGlobPathsBetween dgraph src tgt

{- Benutzung dieser Methode derzeit auskommentiert - wird wahrscheinlich weggeschmissen -}
{- returns a list of all proven loc-glob paths of the given morphism between
   the given source and target node -}
{-getAllProvenLocGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node 
					  -> Node -> [[LEdge DGLinkLab]]
getAllProvenLocGlobPathsOfMorphismBetween dgraph morphism src tgt =
  filterPathsByMorphism morphism allPaths

  where
      allPaths = getAllProvenLocGlobPathsBetween dgraph src tgt
-}
{- returns all paths from the given list whose morphism is equal to the
   given one-}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
		      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths = 
  [path| path <- paths, (calculateMorphismOfPath path) == (Just morphism)]


{- returns a list of all paths to the given node
   that consist of globalDef edges only
   or
   that consist of a localDef edge followed by any number of globalDef edges -}
getAllLocGlobDefPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllLocGlobDefPathsTo dgraph node path =
  (node,path):(locGlobPaths ++
    (concat (
      [getAllLocGlobDefPathsTo dgraph (getSourceNode edge) path| 
       (_, path@(edge:edges)) <- globalPaths]))
    )

  where
    inEdges = inn dgraph node
    globalEdges = filter isGlobalDef inEdges
    localEdges = filter isLocalDef inEdges
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    locGlobPaths = [(getSourceNode edge, (edge:path))| edge <- localEdges]


{- returns all paths consisting of global edges only
   or
   of one local edge followed by any number of global edges-}
getAllLocGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllLocGlobPathsBetween dgraph src tgt =
  locGlobPaths ++ globPaths

  where
    outEdges = out dgraph src
    locEdges = [(edge,target)|edge@(_,target,_) <- 
		(filterByTypes [isLocalEdge] outEdges)]
    locGlobPaths = (concat [map ([edge]++) 
		      (getAllPathsOfTypesBetween dgraph [isGlobalEdge] node tgt [])|
			 (edge,node) <- locEdges])
    globPaths = getAllPathsOfTypesBetween dgraph [isGlobalEdge] src tgt []


{- returns all paths of globalDef edges or globalThm edges 
   between the given source and target node -}
getAllGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypesBetween dgraph [isGlobalDef,isGlobalThm] src tgt []


{- gets all paths consisting of local/global thm/def edges
   of the given morphism -}
getAllThmDefPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
				  -> [[LEdge DGLinkLab]]
getAllThmDefPathsOfMorphismBetween dgraph morphism src tgt =
  filterPathsByMorphism morphism allPaths

  where
    allPaths = getAllPathsOfTypesBetween dgraph types src tgt []
    types = 
      [isGlobalThm,
       isProvenLocalThm,
       isProvenLocalThm,
       isUnprovenLocalThm,
       isGlobalDef,
       isLocalDef]


{- returns all paths of globalDef edges between the given source and 
   target node -}
getAllGlobDefPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobDefPathsBetween dgraph src tgt =
  getAllPathsOfTypeBetween dgraph isGlobalDef src tgt


{- returns all paths consiting of edges of the given type between the
   given node -}
getAllPathsOfTypeBetween :: DGraph -> (LEdge DGLinkLab -> Bool) -> Node
			    -> Node -> [[LEdge DGLinkLab]]
getAllPathsOfTypeBetween dgraph isType src tgt =
  getAllPathsOfTypesBetween dgraph (isType:[]) src tgt []

{- returns all paths consisting of edges of the given types between
   the given nodes -}
getAllPathsOfTypesBetween :: DGraph -> [LEdge DGLinkLab -> Bool] -> Node 
			     -> Node -> [LEdge DGLinkLab]
			     -> [[LEdge DGLinkLab]]
getAllPathsOfTypesBetween dgraph types src tgt path =
  [edge:path| edge <- edgesFromSrc]
          ++ (concat 
               [getAllPathsOfTypesBetween dgraph types src nextTgt (edge:path)|
               (edge,nextTgt) <- nextStep] )

  where
    inGoingEdges = inn dgraph tgt
    edgesOfTypes = filterByTypes types inGoingEdges
    edgesFromSrc = 
	[edge| edge@(source,_,_) <- edgesOfTypes, source == src]
    nextStep =
	[(edge, source)| edge@(source,_,_) <- edgesOfTypes, source /= src]


-- removes all edges that are not of the given types
filterByTypes :: [LEdge DGLinkLab -> Bool] -> [LEdge DGLinkLab]
	      -> [LEdge DGLinkLab]
filterByTypes [] edges = []
filterByTypes (isType:typeChecks) edges =
  (filter isType edges)++(filterByTypes typeChecks edges)


-- --------------------------------------
-- methods to determine or get morphisms
-- --------------------------------------

-- determines the morphism of a given path
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath [] = Nothing
calculateMorphismOfPath path@((src,tgt,edgeLab):furtherPath) =
  case maybeMorphismOfFurtherPath of
    Nothing -> if null furtherPath then Just morphism else Nothing
    Just morphismOfFurtherPath ->
           resultToMaybe $ compHomInclusion morphism morphismOfFurtherPath

  where
    morphism = dgl_morphism edgeLab
    maybeMorphismOfFurtherPath = calculateMorphismOfPath furtherPath


-- ------------------------------------
-- methods to get the nodes of an edge
-- ------------------------------------
getSourceNode :: LEdge DGLinkLab -> Node
getSourceNode (source,_,_) = source

{- Benutzung derzeit auskommentiert ... -}
{-getTargetNode :: LEdge DGLinkLab -> Node
getTargetNode (_,target,_) = target -}


-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------
isProven :: LEdge DGLinkLab -> Bool
isProven edge = isGlobalDef edge || isLocalDef edge 
		|| isProvenGlobalThm edge || isProvenLocalThm edge

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
    (GlobalThm (Proven _) _ _) -> True
    otherwise -> False

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) = 
  case dgl_type edgeLab of
    (GlobalThm Static.DevGraph.Open _ _) -> True
    otherwise -> False

isProvenLocalThm :: LEdge DGLinkLab -> Bool
isProvenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm (Proven _) _ _) -> True
    otherwise -> False

isUnprovenLocalThm :: LEdge DGLinkLab -> Bool
isUnprovenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm (Static.DevGraph.Open) _ _) -> True
    otherwise -> False

isGlobalDef :: LEdge DGLinkLab -> Bool
isGlobalDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    GlobalDef -> True
    otherwise -> False

isLocalDef :: LEdge DGLinkLab -> Bool
isLocalDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    LocalDef -> True
    otherwise -> False

-- ----------------------------------------------------------------------------
-- methods to determine the labels of the inserted edges in the given dgchange
-- ----------------------------------------------------------------------------

{- filters the list of changes for insertions of edges and returns the label
   of one of these; or Nothing if no insertion was found -}
getLabelsOfInsertedEdges :: [DGChange] -> [DGLinkLab]
getLabelsOfInsertedEdges changes = 
  [label | (_,_,label) <- getInsertedEdges changes]

{- returns all insertions of edges from the given list of changes -}
getInsertedEdges :: [DGChange] -> [LEdge DGLinkLab]
getInsertedEdges [] = []
getInsertedEdges (change:list) = 
  case change of
    (InsertEdge edge) -> edge:(getInsertedEdges list)
    otherwise -> getInsertedEdges list

-- ----------------------------------------
-- methods to check and select proof basis
-- ----------------------------------------

{- determines all proven paths in the given list and tries to selet a
   proof basis from these (s. selectProofBasisAux);
   if this fails the same is done for the rest of the given paths, i.e.
   for the unproven ones -}
selectProofBasis :: DGLinkLab -> [[LEdge DGLinkLab]] -> [DGLinkLab]
selectProofBasis label paths =
  if null provenProofBasis then selectProofBasisAux label unprovenPaths
   else provenProofBasis

  where 
    provenPaths = filterProvenPaths paths
    provenProofBasis = selectProofBasisAux label provenPaths
    unprovenPaths = [path | path <- paths, notElem path provenPaths]

{- selects the first path that does not form a proof cycle with the given
 label (if such a path exits) and returns the labels of its edges -}
selectProofBasisAux :: DGLinkLab -> [[LEdge DGLinkLab]] -> [DGLinkLab]
selectProofBasisAux _ [] = []
selectProofBasisAux label (path:list) =
    if notProofCycle label path then nub (calculateProofBasis path)
     else selectProofBasisAux label list


{- calculates the proofBasis of the given path,
 i.e. the list of all DGLinkLabs the proofs of the edges contained in the path
 are based on, plus the DGLinkLabs of the edges themselves;
 duplicates are not removed here, but in the calling method
 selectProofBasisAux -}
calculateProofBasis :: [LEdge DGLinkLab] -> [DGLinkLab]
calculateProofBasis [] = []
calculateProofBasis ((_,_,lab):edges) =
  lab:((getProofBasis lab)++(calculateProofBasis edges))


{- returns the proofBasis contained in the given DGLinkLab -}
getProofBasis :: DGLinkLab -> [DGLinkLab]
getProofBasis lab =
  case dgl_type lab of 
    (GlobalThm (Proven proofBasis) _ _) -> proofBasis
    (LocalThm (Proven proofBasis) _ _) -> proofBasis
    _ -> []


{- returns all proven paths from the given list -}
filterProvenPaths :: [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterProvenPaths [] = []
filterProvenPaths (path:list) =
  if (and [isProven edge| edge <- path]) then path:(filterProvenPaths list)
   else filterProvenPaths list

{- opposite of isProofCycle -}
notProofCycle :: DGLinkLab -> [LEdge DGLinkLab] -> Bool
notProofCycle label  = not.(isProofCycle label)

{- checks if the given label is contained in the ProofBasis of one of the
   edges of the given path -}
isProofCycle :: DGLinkLab -> [LEdge DGLinkLab] -> Bool
isProofCycle _ [] = False
isProofCycle label (edge:path) =
  if (elemOfProofBasis label edge) then True else (isProofCycle label path)

{- checks if the given label is contained in the ProofBasis of the given 
   edge -}
elemOfProofBasis :: DGLinkLab -> (LEdge DGLinkLab) -> Bool
elemOfProofBasis label (_,_,dglink) =
  case dgl_type dglink of 
    (GlobalThm (Proven proofBasis) _ _) -> elem label proofBasis
    (LocalThm (Proven proofBasis) _ _) -> elem label proofBasis
    _ -> False

sensOfNode :: DGraph -> DGNodeLab -> G_l_sentence_list
sensOfNode dg (DGNode {dgn_sens = sens}) = sens
sensOfNode dg _ = undefined -- ??? to simplistic

-- | Calculate the morphism of a path with given start node
calculateMorphismOfPathWithStart :: DGraph -> (Node,[LEdge DGLinkLab]) 
                                           -> Maybe GMorphism
calculateMorphismOfPathWithStart dg (n,[]) = do
  ctx <- fst $ match n dg
  return $ ide Grothendieck (dgn_sign (lab' ctx)) -- ??? to simplistic 
  
calculateMorphismOfPathWithStart _ (_,p) = calculateMorphismOfPath p

-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: DGraph -> Node -> Result (G_sign,G_l_sentence_list) 
computeTheory dg n = do
  ctx <- maybeToResult nullPos ("Could node find node "++show n)
              $ fst $ match n dg
  let  nlab = lab' ctx
       paths = getAllLocGlobDefPathsTo dg n []
  mors <- maybeToResult nullPos "Could not calculate morphism of path"
            $ sequence $ map (calculateMorphismOfPathWithStart dg) paths
  ctxs <- maybeToResult nullPos "Could not find start node of path"
            $ sequence $ map (fst . flip match dg . fst) paths
  let sens = map (sensOfNode dg . lab') ctxs
  sens' <- sequence 
            $ map (uncurry translateG_l_sentence_list) 
            $ zip mors sens
  sens'' <- maybeToResult nullPos "Logic mismatch for sentences"
              $ flatG_l_sentence_list sens'
  return (dgn_sign nlab,sens'') -- ??? dgn_sign too simplistic 

-- ---------------
-- basic inference
-- ---------------

getGoals :: DGraph -> LEdge DGLinkLab -> Result G_l_sentence_list
getGoals dg (n,_,edge) = do
  ctx <- maybeToResult nullPos ("Could node find node "++show n)
              $ fst $ match n dg
  let nlab = lab' ctx  
      sens = dgn_sens nlab -- ??? To simplistic
      mor = dgl_morphism edge
  translateG_l_sentence_list mor sens

getProvers :: LogicGraph -> AnyLogic -> [(G_prover,AnyComorphism)]
getProvers lg (Logic lid) =
  [(G_prover (targetLogic cid) p,Comorphism cid) | 
        (_,Comorphism cid) <- cms,
        language_name (sourceLogic cid) == language_name lid,
        p <- provers (targetLogic cid)]
  where cms = Map.toList 
               $ Map.insert ("Id_"++language_name lid)
                            (Comorphism (IdComorphism lid))
               $ comorphisms lg
        -- ??? Should be composites as well!
        -- ??? Sublogic check is missing!
         

selectProver :: [(G_prover,AnyComorphism)] -> IOResult (G_prover,AnyComorphism)
selectProver [p] = return p
selectProver [] = resToIORes $ fatal_error "No pover available" nullPos
selectProver (p:_) = return p -- ??? to simplistic
 
-- applies basic inference to a given node
basicInferenceNode ::  LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicInferenceNode lg (ln,node) proofStatus@(globalContext,history,dGraph) =
  ioresToIO (do 
    (G_sign lid1 sign,G_l_sentence_list lid2 axs) <- 
         resToIORes $ computeTheory dGraph node
    let inEdges = inn dGraph node
        localEdges = filter isUnprovenLocalThm inEdges
    goalslist <- resToIORes $ sequence $ map (getGoals dGraph) localEdges
    G_l_sentence_list lid3 goals <- 
      if null goalslist then return $ G_l_sentence_list lid2 [] 
        else resToIORes (maybeToResult nullPos "Logic mismatch for proof goals" 
                                  (flatG_l_sentence_list goalslist))
    let provers = getProvers lg (Logic lid1)
    (G_prover lid4 p,Comorphism cid) <- selectProver provers
    let lidS = sourceLogic cid
        lidT = targetLogic cid
    sign' <- resToIORes $ rcoerce lidS lid1 nullPos sign
    axs' <- resToIORes $ rcoerce lidS lid2 nullPos axs
    goals' <- resToIORes $ rcoerce lidS lid3 nullPos goals
    p' <- resToIORes $ rcoerce lidT lid4 nullPos p
    -- Borrowing: translate theory and goal
    (sign'',sens'') <- resToIORes  
                        $ maybeToResult nullPos "Could not map signature"
                        $ map_sign cid sign'
    axs'' <- resToIORes
                 $ maybeToResult nullPos "Could not map sentences"
                 $ sequence 
                 $ map (mapNamedM (map_sentence cid sign')) axs'
    goals'' <- resToIORes
                 $ maybeToResult nullPos "Could not map sentences"
                 $ sequence 
                 $ map (mapNamedM (map_sentence cid sign')) goals'
    -- compute name ot theory
    ctx <- resToIORes 
                $ maybeToResult nullPos ("Could node find node "++show node)
                $ fst $ match node dGraph
    let nlab = lab' ctx  
        nodeName = case nlab of
          DGNode _ _ _ _-> dgn_name nlab
          DGRef _ _ _ -> dgn_renamed nlab
        thName = showPretty (getLIB_ID ln) "_"
                 ++ maybe (show node) (flip showPretty "") nodeName
    ps <- ioToIORes $ prove p' thName (sign'',sens''++axs'') goals'' 
    let nextDGraph = dGraph -- ??? to be implemented
        nextHistoryElem = undefined -- ??? to be implemented
    return (globalContext, {- nextHistoryElem: -} history, nextDGraph)
   )