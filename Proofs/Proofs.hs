{- HetCATS/Proofs/Proofs.hs
   $Id$
   Till Mossakowski

   Proofs in development graphs.

   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus. In: CASL reference manual, part IV.
   Available from http://www.cofi.info

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
import Static.DevGraph
import Common.Lib.Graph

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
 -- obsolete | LocDecompI
 -- obsolete | LocDecompII
 | GlobSubsumption (LEdge DGLinkLab)
 -- obsolete  | LocSubsumption (LEdge DGLinkLab)
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
    newHistoryElem = 
      if null newChanges then historyElem
       else (((GlobDecomp edge):(fst historyElem)),
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
    proofBasis =
      case getLabelOfAnyInsertedEdge changes of
        Nothing -> []
        Just label -> label:[]
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
globSubsumeAux dGraph historyElement [] = (dGraph, historyElement)
globSubsumeAux dGraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  if null allPaths
   then
     globSubsumeAux dGraph (rules,changes) list
   else 
     globSubsumeAux (insEdge newEdge (delLEdge ledge dGraph)) (newRules,newChanges) list

  where
    morphism = dgl_morphism edgeLab
    allPaths = getAllProvenGlobPathsOfMorphismBetween dGraph morphism src tgt
    proofBasis =
      case allPaths of
        [] -> []
        (path:paths) -> map getLabelOfEdge path
    (GlobalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (GlobalThm (Proven proofBasis)
				   conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newRules = (GlobSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)


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
    allPaths = getAllThmDefPathsOfMorphismBetween dgraph morphism src tgt 
--	getAllProvenLocGlobPathsOfMorphismBetween dgraph morphism source target
    proofBasis = selectProofBasis edgeLab allPaths
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


-- -----------------------------------------------------------------------
-- methods that check if paths of certain types exist between given nodes
-- -----------------------------------------------------------------------

{- checks if there is a path of globalDef edges or proven globalThm edges
   with the given morphism between the given source and target node -}
existsProvenGlobPathOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
				    -> Bool
existsProvenGlobPathOfMorphismBetween dgraph morphism src tgt =
  elem morphism filteredMorphismsOfProvenPaths

    where
      allPaths = getAllProvenGlobPathsBetween dgraph src tgt
      morphismsOfPaths = map calculateMorphismOfPath allPaths
      filteredMorphismsOfProvenPaths = getFilteredMorphisms morphismsOfPaths 

{- returns a list of all proven global paths of the given morphism between
   the given source and target node-}
getAllProvenGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
					  -> [[LEdge DGLinkLab]]
getAllProvenGlobPathsOfMorphismBetween dgraph morphism src tgt = 
  filterPathsByMorphism morphism allPaths

  where 
      allPaths = getAllProvenGlobPathsBetween dgraph src tgt


{- returns a list of all proven loc-glob paths of the given morphism between
   the given source and target node -}
getAllProvenLocGlobPathsOfMorphismBetween :: DGraph -> GMorphism -> Node 
					  -> Node -> [[LEdge DGLinkLab]]
getAllProvenLocGlobPathsOfMorphismBetween dgraph morphism src tgt =
  filterPathsByMorphism morphism allPaths

  where
      allPaths = getAllProvenLocGlobPathsBetween dgraph src tgt

{- returns all paths from the given list whose morphism is equal to the
   given one-}
filterPathsByMorphism :: GMorphism -> [[LEdge DGLinkLab]]
		      -> [[LEdge DGLinkLab]]
filterPathsByMorphism morphism paths = 
  [path| path <- paths, (calculateMorphismOfPath path) == (Just morphism)]

{- @@@ hier weiter machen @@@ -}
{- returns a Maybe path the proof of the given edge can be based on -}
{-getUnprovenGlobPathToBaseOn :: DGraph -> GMorphism -> LEdge DGLinkLab
					   -> Maybe [LEdge DGLinkLab]
getUnprovenGlobPathToBaseOn dgraph morphism ledge@(src,tgt,_) =
  if null filteredPathsToBaseOn then Nothing
   else Just (head filteredPathsToBaseOn)

    where
      allPaths = getAllUnprovenGlobPathsBetween dgraph src tgt
      allPathsToBaseOn = filterPathsToBaseOn allPaths ledge
      pathsWithMorphisms = [(calculateMorphismOfPath path,path)|
			    path <- allPathsToBaseOn]
      filteredPathsWithMorphisms = filterMorphisms pathsWithMorphisms
      filteredPathsToBaseOn = [path|(morph,path) <- filteredPathsWithMorphisms,
			       morph == morphism]
-}
{- checks if a path consisting of globalDef edges only
   or consisting of a localDef edge followed by any number of globalDef edges
   exists between the given nodes -}
existsLocGlobDefPathOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
                                        -> Bool
existsLocGlobDefPathOfMorphismBetween dgraph morphism src tgt =
  elem morphism filteredMorphismsOfLocGlobDefPaths

    where
      allPaths = getAllLocGlobDefPathsBetween dgraph src tgt
      morphismsOfPaths = map calculateMorphismOfPath allPaths
      filteredMorphismsOfLocGlobDefPaths = 
	  getFilteredMorphisms morphismsOfPaths

existsProvenLocGlobPathOfMorphismBetween :: DGraph -> GMorphism -> Node
					 -> Node -> Bool
existsProvenLocGlobPathOfMorphismBetween dgraph morphism src tgt =
  elem morphism filteredMorphismsOfProvenLocGlobPaths

    where
      allPaths = getAllProvenLocGlobPathsBetween dgraph src tgt
      morphismsOfPaths = map calculateMorphismOfPath allPaths
      filteredMorphismsOfProvenLocGlobPaths = 
	  getFilteredMorphisms morphismsOfPaths


-- ----------------------------------------------
-- methods that calculate paths of certain types
-- ----------------------------------------------
-- @@@ this method is not used at the momen!! @@@
{- returns a list of all paths to the given node
   that consist of globalDef edges or proven global theorems only
   or
   that consist of a localDef/proven local theorem edge followed by
   any number of globalDef/proven global theorem edges -}
getAllProvenLocGlobPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
getAllProvenLocGlobPathsTo dgraph node path =
  (node,path):(locGlobPaths ++ 
    (concat (
      [getAllProvenLocGlobPathsTo dgraph (getSourceNode edge) path| 
       (_, path@(edge:edges)) <- globalPaths]))
  )

  where
    inEdges = inn dgraph node
    globalEdges = (filter isGlobalDef inEdges) 
		  ++ (filter isProvenGlobalThm inEdges)
    localEdges = (filter isLocalDef inEdges) 
		 ++ (filter isProvenLocalThm inEdges)
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    locGlobPaths = [(getSourceNode edge, (edge:path))| edge <- localEdges]

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

{- returns all paths consisting of globalDef and proven global thm edges only
   or
   of one localDef or proven local thm followed by any number of globalDef or
   proven global thm edges-}
getAllProvenLocGlobPathsBetween :: DGraph -> Node -> Node 
				     -> [[LEdge DGLinkLab]]
getAllProvenLocGlobPathsBetween dgraph src tgt =
  getAllLocGlobPathsOfTypesBetween dgraph src tgt 
    [isLocalDef,isProvenLocalThm] [isGlobalDef,isProvenGlobalThm]

{- returns all paths consisting only of edges of the types in the snd list
   or
   of one edge of one of the types of the fst list followed by any number
   of edges of the types of the snd list -}
getAllLocGlobPathsOfTypesBetween :: DGraph -> Node -> Node -> [LEdge DGLinkLab -> Bool] -> [LEdge DGLinkLab -> Bool] -> [[LEdge DGLinkLab]]
getAllLocGlobPathsOfTypesBetween dgraph src tgt locTypes globTypes =
  locGlobPaths ++ globPaths

  where
    outEdges = out dgraph src
    locEdges = [(edge,getTargetNode edge)|edge <- 
		(filterByTypes locTypes outEdges)]
    locGlobPaths = (concat [map ([edge]++) 
		      (getAllPathsOfTypesBetween dgraph globTypes node tgt [])|
			 (edge,node) <- locEdges])
    globPaths = getAllProvenGlobPathsBetween dgraph src tgt
    

{- returns all paths of globalDef edges or proven globalThm edges 
   between the given source and target node -}
getAllProvenGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllProvenGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypesBetween dgraph [isGlobalDef,isProvenGlobalThm] src tgt []


{- returns all paths of globalDef edges between the given source and 
   target node -}
getAllGlobDefPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllGlobDefPathsBetween dgraph src tgt =
  getAllPathsOfTypeBetween dgraph isGlobalDef src tgt


{- returns all paths of unproven global thm edges between the given
   source and target node -}
getAllUnprovenGlobPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllUnprovenGlobPathsBetween dgraph src tgt =
  getAllPathsOfTypeBetween dgraph isUnprovenGlobalThm src tgt

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


{- returns a list of all paths between the given nodes
   that consist only of globalDef edges
   or
   that consist of a localDef edge followed by any number of globalDef edges -}
getAllLocGlobDefPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllLocGlobDefPathsBetween dgraph src tgt = globDefPaths ++ locGlobDefPaths

  where
    globDefPaths = getAllGlobDefPathsBetween dgraph src tgt
    outEdges = out dgraph src
    nextStep = [(edge,getTargetNode edge) | edge <- outEdges]
    pathEnds =
	[(edge,getAllGlobDefPathsBetween dgraph node tgt)|
		(edge, node) <- nextStep]
    locGlobDefPaths =
	concat [addToAll edge paths | (edge, paths) <- pathEnds]


-- adds the given element at the front of all lists in the given list
addToAll :: a -> [[a]] -> [[a]]
addToAll _ [] = []
addToAll element (list:lists) = (element:list):(addToAll element lists)


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
		  comp Grothendieck morphism morphismOfFurtherPath

  where
    morphism = dgl_morphism edgeLab
    maybeMorphismOfFurtherPath = calculateMorphismOfPath furtherPath

{- removes the "Nothing"s from a list of Maybe GMorphism
   returns the remaining elements as plain GMorphisms -}
getFilteredMorphisms :: [Maybe GMorphism] -> [GMorphism]
getFilteredMorphisms morphisms =
  [morph| (Just morph) <- filter isValidMorphism morphisms]

-- returns True if the given Maybe GMorphisms is not "Nothing"
isValidMorphism :: Maybe GMorphism -> Bool
isValidMorphism morphism =
  case morphism of
    Nothing -> False
    Just _  -> True


-- ------------------------------------
-- methods to get the nodes of an edge
-- ------------------------------------
getSourceNode :: LEdge DGLinkLab -> Node
getSourceNode (source,_,_) = source

getTargetNode :: LEdge DGLinkLab -> Node
getTargetNode (_,target,_) = target


-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------
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

-- ---------------------------------------------------------------
-- methods to determine whether a proof is based on the given edge
-- ----------------------------------------------------------------

{- filters all paths out of the given list whose proof is not based
   on the given edge -}
filterPathsToBaseOn :: [[LEdge DGLinkLab]] -> LEdge DGLinkLab 
		 -> [[LEdge DGLinkLab]]
filterPathsToBaseOn [] _ = []
filterPathsToBaseOn (path:list) ledge =
  case (and [isNotBasedOn status ledge| status <- statusList]) of
    True -> path:(filterPathsToBaseOn list ledge)
    False -> filterPathsToBaseOn list ledge
  where 
    labelList = [dgl_type label|(_,_,label) <- path]
    statusList = getThmLinkStatus labelList

{- checks if the given proof is NOT based on the given edge -}
isNotBasedOn :: ThmLinkStatus -> LEdge DGLinkLab -> Bool
isNotBasedOn status ledge = not (isBasedOn status ledge)

{- checks if the given proof is based on the given edge -}
isBasedOn :: ThmLinkStatus -> LEdge DGLinkLab -> Bool
isBasedOn Static.DevGraph.Open _ = False
isBasedOn (Proven []) _ = False
isBasedOn (Proven list) ledge@(_,_,edgelab) =
    (elem edgelab list)
    || or [isBasedOn status ledge|status <- statusList]
  where 
    labelList = map dgl_type list
    statusList = getThmLinkStatus labelList

{- returns the status of proof of a list of edges -}
getThmLinkStatus :: [DGLinkType] -> [ThmLinkStatus]
getThmLinkStatus [] = []
getThmLinkStatus (edgeType:list) =
  case edgeType of
    GlobalThm status _ _ -> status:(getThmLinkStatus list)
    LocalThm status _ _ -> status:(getThmLinkStatus list)
    otherwise -> error ("getThmLinkStatus not yet implemented for "
		       ++(show edgeType))

{- filters the list of changes for insertions of edges and returns the label of one of these; or Nothing if no insertion was found -}
getLabelOfAnyInsertedEdge :: [DGChange] -> Maybe DGLinkLab
getLabelOfAnyInsertedEdge changes = 
  case getInsertedEdges changes of
    [] -> Nothing
    ((_,_,label):edges) -> Just label

{- returns all insertions of edges from the given list of changes -}
getInsertedEdges :: [DGChange] -> [LEdge DGLinkLab]
getInsertedEdges [] = []
getInsertedEdges (change:list) = 
  case change of
    (InsertEdge edge) -> edge:(getInsertedEdges list)
    otherwise -> getInsertedEdges list

-- -- ------------------------------------------------------
-- @@@@@@@ ueberpruefung der proofBasis einfuehren...
{- wenn die Proofbasis angelegt wird gucken, ob der erste pfad kanten enthält, die die zu beweisende kante in ihrer proofbasis haben, falls ja, mit dem nächsten versuchen usw., falls nein: nehmen
-}


{- gets all paths consisting of local/global thm/def edges
   of the given morphism -}
getAllThmDefPathsOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
				  -> [[LEdge DGLinkLab]]
getAllThmDefPathsOfMorphismBetween dgraph morphism src tgt =
  filterPathsByMorphism morphism allPaths

  where
    allPaths = getAllPathsOfTypesBetween dgraph types src tgt []
    types = 
      [isProvenGlobalThm,
       isUnprovenGlobalThm,
       isProvenLocalThm,
       isProvenLocalThm,
       isUnprovenLocalThm,
       isGlobalDef,
       isLocalDef]

{- selects the first path that does not form a proof cycle with the given
 label (if such a path exits) and returns the labels of its edges -}
selectProofBasis :: DGLinkLab -> [[LEdge DGLinkLab]] -> [DGLinkLab]
selectProofBasis _ [] = []
selectProofBasis label (path:list) =
  if notProofCycle label path then [lab|(_,_,lab)<- path]
   else selectProofBasis label list

{- opposite of isProofCycle -}
notProofCycle :: DGLinkLab -> [LEdge DGLinkLab] -> Bool
notProofCycle label  = not.(isProofCycle label)

{- checks if the given label is contained in the ProofBasis of one of the edges of the given path -}
isProofCycle :: DGLinkLab -> [LEdge DGLinkLab] -> Bool
isProofCycle _ [] = False
isProofCycle label (edge:path) =
  if (elemOfProofBasis label edge) then True else (isProofCycle label path)

{- checks if the given label is contained in the ProofBasis of the given edge -}
elemOfProofBasis :: DGLinkLab -> (LEdge DGLinkLab) -> Bool
elemOfProofBasis label (_,_,dglink) =
  case dgl_type dglink of 
    (GlobalThm (Proven proofBasis) _ _) -> elem label proofBasis
    (LocalThm (Proven proofBasis) _ _) -> elem label proofBasis
    _ -> False