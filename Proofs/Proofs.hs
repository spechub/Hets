{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
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

todo in general:

Order of rule application: try to use local links induced by %implies 
for subsumption proofs (such that the %implied formulas need not be
re-proved)

Integrate stuff from Saarbrücken
Add proof status information

 what should be in proof status:

- proofs of thm links according to rules
- cons, def and mono annos, and their proofs

todo for Jorina:


   todo:
   - bei GlobDecomp hinzufügen:
     zusätzlich alle Pfade K<--theta-- M --sigma-->N in den aktuellen 
     Knoten N, die mit einem HidingDef anfangen, und danach nur GlobalDef
     theta ist der Signaturmorphismus des HidingDef's (geht "falsch rum")
     sigma ist die Komposition der Signaturmorphismen auf dem restl. Pfad
     für jeden solchen Pfad: einen HidingThm theta einfügen. sigma ist
     der normale Morphismus (wie bei jedem anderen Link)
     siehe auch Seite 302 des CASL Reference Manual
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


{-
   proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}

type ProofStatus = (GlobalContext,LibEnv,[([DGRule],[DGChange])],DGraph)

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
  deriving (Eq)
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
globDecomp proofStatus@(globalContext,libEnv,history,dgraph) =
  (globalContext, libEnv, ((newHistoryElem):history), newDgraph)

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
    pathsToSource
      = getAllLocOrHideGlobDefPathsTo dgraph (getSourceNode edge) []
    paths = [(node, path++(edge:[]))| (node,path) <- pathsToSource]

{- auxiliary funktion for globDecompForOneEdge (above)
   actual implementation -}
globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange] ->
			   [(Node, [LEdge DGLinkLab])] -> (DGraph,[DGChange])
{- if the list of paths is empty from the beginning, nothing is done
   otherwise the unprovenThm edge is replaced by a proven one -}
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes [] = 
  if null changes then (dgraph, changes)
   else
     if isDuplicate provenEdge dgraph changes
            then (delLEdge edge dgraph,
	    ((DeleteEdge edge):changes))
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
  if isDuplicate newEdge dgraph changes
    then globDecompForOneEdgeAux dgraph edge changes list
   else globDecompForOneEdgeAux newGraph edge newChanges list

  where
    isHiding = not (null path) && isHidingDef (head path)
    morphismPath = if isHiding then tail path else path
    morphism = case calculateMorphismOfPath morphismPath of
                 Just morph -> morph
                 Nothing ->
	           error "globDecomp: could not determine morphism of new edge"
    newEdge = if isHiding then hidingEdge else localEdge
    hidingEdge = 
       (node,
        target,
        DGLink {dgl_morphism = morphism,
                dgl_type = (HidingThm (dgl_morphism (getLabelOfEdge (head path))) (Static.DevGraph.Open)),
                dgl_origin = DGProof})
    localEdge = (node,
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
globSubsume proofStatus@(globalContext,libEnv,history,dGraph) =
  (globalContext, libEnv, nextHistoryElem:history, nextDGraph)

  where
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dGraph)
    result = globSubsumeAux libEnv dGraph ([],[]) globalThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

{- auxiliary function for globSubsume (above)
   the actual implementation -}
globSubsumeAux :: LibEnv ->  DGraph -> ([DGRule],[DGChange]) ->
		  [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux _ dgraph historyElement [] = (dgraph, historyElement)
globSubsumeAux libEnv dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if not (null proofBasis) || isIdentityEdge ledge libEnv dgraph
   then
     if isDuplicate newEdge dgraph changes then
        globSubsumeAux libEnv (delLEdge ledge dgraph) 
          (newRules,(DeleteEdge ledge):changes) list
      else
        globSubsumeAux libEnv (insEdge newEdge (delLEdge ledge dgraph))
          (newRules,(DeleteEdge ledge):((InsertEdge newEdge):changes)) list
   else 
     globSubsumeAux libEnv dgraph (rules,changes) list

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

-- --------------------
-- local decomposition
-- --------------------

{- a merge of the rules local subsumption, local decomposition I and 
   local decomposition II -}
-- applies this merge of rules to all unproven localThm edges if possible
locDecomp ::  ProofStatus -> ProofStatus
locDecomp proofStatus@(globalContext,libEnv,history,dGraph) =
  (globalContext, libEnv, nextHistoryElem:history, nextDGraph)

  where
    localThmEdges = filter isUnprovenLocalThm (labEdges dGraph)
    result = locDecompAux libEnv dGraph ([],[]) localThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

{- auxiliary function for locDecomp (above)
   actual implementation -}
locDecompAux :: LibEnv -> DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locDecompAux libEnv dgraph historyElement [] = (dgraph, historyElement)
locDecompAux libEnv dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if (null proofBasis && not (isIdentityEdge ledge libEnv dgraph))
     then
       locDecompAux libEnv dgraph (rules,changes) list
     else
       if isDuplicate newEdge dgraph changes
          then locDecompAux libEnv auxGraph 
                 (newRules,(DeleteEdge ledge):changes) list
       else locDecompAux libEnv newGraph (newRules,newChanges) list

  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllLocGlobPathsBetween dgraph src tgt
    sens = getSentenceList libEnv dgraph src
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


{- returns the sentence list of the given node -}
getSentenceList :: LibEnv -> DGraph -> Node -> Maybe G_l_sentence_list
getSentenceList libEnv dgraph node =
  if isDGRef nodeLab
    then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> getSentenceList libEnv refDgraph (dgn_node nodeLab)
      Nothing -> Nothing
    else Just (dgn_sens nodeLab)
    where nodeLab = lab' (context node dgraph)


{- returns the sentence list of the given node -}
getSignature :: LibEnv -> DGraph -> Node -> Maybe G_sign
getSignature libEnv dgraph node =
  if isDGRef nodeLab
    then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> 
         getSignature libEnv refDgraph (dgn_node nodeLab)
      Nothing -> Nothing
    else Just (dgn_sign nodeLab)
    where nodeLab = lab' (context node dgraph)

{- removes all paths from the given list of paths whose morphism does not translate the given sentence list to the same resulting sentence list as the given morphism-}
filterByTranslation :: Maybe G_l_sentence_list -> GMorphism -> [[LEdge DGLinkLab]] -> [[LEdge DGLinkLab]]
filterByTranslation maybeSens morphism paths =
  case maybeSens of
    Just sens -> [path| path <- paths, isSameTranslation sens morphism path]
    Nothing -> []
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


{- returns all paths from the given list whose morphism is equal to the
   given one-}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
		      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths = 
  [path| path <- paths, (calculateMorphismOfPath path) == (Just morphism)]


{- returns a list of all paths to the given node
   that consist of globalDef edge only
   or
   that consist of a localDef or hidingDef edge
   followed by any number of globalDef edges -}
getAllLocOrHideGlobDefPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllLocOrHideGlobDefPathsTo =
    getAllGlobDefPathsBeginningWithTypesTo
	([isLocalDef, isHidingDef]::[LEdge DGLinkLab -> Bool])

{- returns a list of all paths to the given node
   that consist of globalDef edges only
   or
   that consist of a localDef edge followed by any number of globalDef edges -}
getAllLocGlobDefPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllLocGlobDefPathsTo = getAllGlobDefPathsBeginningWithTypesTo 
			      ([isLocalDef]::[LEdge DGLinkLab -> Bool])
{-  (node,path):(locGlobPaths ++
    (concat (
      [getAllLocGlobDefPathsTo dgraph (getSourceNode edge) path| 
       (_, path@(edge:edges)) <- globalPaths]))
    )

  where
    inEdges = inn dgraph node
    globalEdges = [edge| edge <- filter isGlobalDef inEdges, notElem edge path]
    localEdges = [edge| edge <- filter isLocalDef inEdges, notElem edge path]
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    locGlobPaths = [(getSourceNode edge, (edge:path))| edge <- localEdges]
-}

{- returns a list of all paths to the given node
   that consist of globalDef edges only
   or
   that consist of an edge of one of the given types
   followed by any number of globalDef edges -}
getAllGlobDefPathsBeginningWithTypesTo :: [LEdge DGLinkLab -> Bool] -> DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllGlobDefPathsBeginningWithTypesTo types dgraph node path =
  (node,path):(typeGlobPaths ++
    (concat ( [getAllGlobDefPathsBeginningWithTypesTo
                   types dgraph (getSourceNode edge) path |
                       (_, path@(edge:edges)) <- globalPaths])
    )
   )

  where
    inEdges = inn dgraph node
    globalEdges = [edge| edge <- filter isGlobalDef inEdges, notElem edge path]
    edgesOfTypes 
        = [edge| edge <- filterByTypes types inEdges, notElem edge path]
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    typeGlobPaths = [(getSourceNode edge, (edge:path))| edge <- edgesOfTypes]


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
    edgesOfTypes =
        [edge| edge <- filterByTypes types inGoingEdges, notElem edge path]
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

isHidingDef :: LEdge DGLinkLab -> Bool
isHidingDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    HidingDef -> True
    otherwise -> False

-- ----------------------------------------------------------------------------
-- other methods on edges
-- ----------------------------------------------------------------------------
{- returns true, if an identical edge is already in the graph or marked to be inserted,
 false otherwise-}
isDuplicate :: LEdge DGLinkLab -> DGraph -> [DGChange] -> Bool
isDuplicate newEdge dgraph changes = 
  elem (InsertEdge newEdge) changes || elem newEdge (labEdges dgraph)


isIdentityEdge :: LEdge DGLinkLab -> LibEnv -> DGraph -> Bool
isIdentityEdge (src,tgt,edgeLab) libEnv dgraph =
  if isDGRef nodeLab then 
    case Map.lookup (dgn_libname nodeLab) libEnv of
      Just globContext@(_,_,refDgraph) -> isIdentityEdge (dgn_node nodeLab,tgt,edgeLab) libEnv refDgraph
      Nothing -> False
   else if src == tgt && (dgl_morphism edgeLab) == (ide Grothendieck (dgn_sign nodeLab)) then True else False

  where nodeLab = lab' (context src dgraph)


{- returns the DGLinkLab of the given LEdge -}
getLabelOfEdge :: (LEdge b) -> b
getLabelOfEdge (_,_,label) = label

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


-- | Calculate the morphism of a path with given start node
calculateMorphismOfPathWithStart :: DGraph -> (Node,[LEdge DGLinkLab]) 
                                           -> Maybe GMorphism
calculateMorphismOfPathWithStart dg (n,[]) = do
  ctx <- fst $ match n dg
  return $ ide Grothendieck (dgn_sign (lab' ctx)) -- ??? to simplistic 
  
calculateMorphismOfPathWithStart _ (_,p) = calculateMorphismOfPath p

-- | Compute the theory of a node (CASL Reference Manual, p. 294, Def. 4.9)
computeTheory :: LibEnv -> DGraph -> Node -> Result (G_sign,G_l_sentence_list) 
computeTheory libEnv dg n = do
  let  paths = reverse $ getAllLocGlobDefPathsTo dg n []
         -- reverse needed to have a "bottom up" ordering
  mors <- maybeToResult nullPos "Could not calculate morphism of path"
            $ mapM (calculateMorphismOfPathWithStart dg) paths
  sens <- maybeToResult nullPos "Could not calculate sentence list of node"
            $ mapM (getSentenceList libEnv dg . fst) paths
  sens' <- mapM (uncurry translateG_l_sentence_list) 
            $ zip mors sens
  sens'' <- maybeToResult nullPos "Logic mismatch for sentences"
              $ flatG_l_sentence_list sens'
  sig <- maybeToResult nullPos "Could not calculate signature of node"
              $ getSignature libEnv dg n
  return (sig,sens'') 

-- ---------------
-- basic inference
-- ---------------

getGoals :: LibEnv -> DGraph -> LEdge DGLinkLab -> Result G_l_sentence_list
getGoals libEnv dg (n,_,edge) = do
  sens <- maybeToResult nullPos ("Could node find node "++show n)
              $  getSentenceList libEnv dg n
  let mor = dgl_morphism edge
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
basicInferenceNode :: LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicInferenceNode lg (ln,node) 
         proofStatus@(globalContext,libEnv,history,dGraph) =
  ioresToIO (do 
    (G_sign lid1 sign,G_l_sentence_list lid2 axs) <- 
         resToIORes $ computeTheory libEnv dGraph node
    let inEdges = inn dGraph node
        localEdges = filter isUnprovenLocalThm inEdges
    goalslist <- resToIORes $ mapM (getGoals libEnv dGraph) localEdges
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
                        $ map_theory cid (sign',axs')
{-    axs'' <- resToIORes
                 $ maybeToResult nullPos "Could not map sentences"
                 $ mapM (mapNamedM (map_sentence cid sign')) axs' -}
    goals'' <- resToIORes
                 $ maybeToResult nullPos "Could not map sentences"
                 $ mapM (mapNamedM (map_sentence cid sign')) goals'
    -- compute name of theory
    ctx <- resToIORes 
                $ maybeToResult nullPos ("Could node find node "++show node)
                $ fst $ match node dGraph
    let nlab = lab' ctx  
        nodeName = case nlab of
          DGNode _ _ _ _-> dgn_name nlab
          DGRef _ _ _ -> dgn_renamed nlab
        thName = showPretty (getLIB_ID ln) "_"
                 ++ maybe (show node) (flip showPretty "") nodeName
    ps <- ioToIORes $ prove p' thName (sign'',sens'') goals'' 
    let (nextDGraph, nextHistoryElem) = proveLocalEdges dGraph localEdges
--    let nextDGraph = dGraph -- ??? to be implemented
  --      nextHistoryElem = error "Proofs.Proofs: basic inference"
                 -- ??? to be implemented
    return (globalContext, libEnv, nextHistoryElem:history, nextDGraph)
   )

proveLocalEdges :: DGraph -> [LEdge DGLinkLab] -> (DGraph,([DGRule],[DGChange]))
proveLocalEdges dGraph edges = (nextDGraph,([LocalInference],changes))

  where (nextDGraph,(_,changes)) = proveLocalEdgesAux ([],[]) dGraph edges


proveLocalEdgesAux :: ([DGRule],[DGChange]) -> DGraph -> [LEdge DGLinkLab] 
  -> (DGraph,([DGRule],[DGChange]))
proveLocalEdgesAux historyElem dGraph [] = (dGraph, historyElem)
proveLocalEdgesAux (rules,changes) dGraph ((edge@(src, tgt, edgelab)):edges) = 
  if True then proveLocalEdgesAux (rules,(DeleteEdge edge):((InsertEdge provenEdge):changes)) (insEdge provenEdge(delLEdge edge dGraph)) edges
   else proveLocalEdgesAux (rules,changes) dGraph edges

  where
    morphism = dgl_morphism edgelab
    (LocalThm _ conservativity conservStatus) = (dgl_type edgelab)
    proofBasis = [] -- to be implemented
    provenEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven proofBasis)
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )


-- applies consistency checking to a given node
basicCCC :: LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicCCC = error "basicCCC not yet implemented!"

{-
basicCCC lg (ln,node) 
         proofStatus@(globalContext,libEnv,history,dGraph) =
  ioresToIO (do 
    (G_sign lid1 sign,G_l_sentence_list lid2 axs) <- 
         resToIORes $ computeTheory libEnv dGraph node
    let cccs = getCCCs lg (Logic lid1)
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
                 $ mapM (mapNamedM (map_sentence cid sign')) axs'
    goals'' <- resToIORes
                 $ maybeToResult nullPos "Could not map sentences"
                 $ mapM (mapNamedM (map_sentence cid sign')) goals'
    -- compute name of theory
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
    let (nextDGraph, nextHistoryElem) = proveLocalEdges dGraph localEdges
--    let nextDGraph = dGraph -- ??? to be implemented
  --      nextHistoryElem = error "Proofs.Proofs: basic inference"
                 -- ??? to be implemented
    return (globalContext, libEnv, nextHistoryElem:history, nextDGraph)
   )
-}