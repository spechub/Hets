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
 | LocDecompI
 | LocDecompII
 | GlobSubsumption (LEdge DGLinkLab)
 | LocSubsumption (LEdge DGLinkLab)
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
applyRule = undefined

{- apply rule GlobDecomp to all global theorem links in the current DG 
   current DG = DGm
   add to proof status the pair ([GlobDecomp e1,...,GlobDecomp en],DGm+1)
   where e1...en are the global theorem links in DGm
   DGm+1 results from DGm by application of GlobDecomp e1,...,GlobDecomp en -}

globDecomp :: ProofStatus -> ProofStatus
globDecomp proofStatus@(globalContext,history,dgraph) =
  if null (snd newHistoryElem) then proofStatus
   else (globalContext, ((newHistoryElem):history), newDgraph)

  where
    -- nur die unproven oder allgemein die globalThms?
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
    (newDgraph, newHistoryElem) = globDecompAux dgraph globalThmEdges ([],[])

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


globDecompForOneEdge :: DGraph -> LEdge DGLinkLab -> (DGraph,[DGChange])
globDecompForOneEdge dgraph edge =
  globDecompForOneEdgeAux dgraph edge [] paths
  
  where
    paths = getAllProvenLocGlobPathsTo dgraph (getSourceNode edge) []


globDecompForOneEdgeAux :: DGraph -> LEdge DGLinkLab -> [DGChange] ->
			   [(Node, [LEdge DGLinkLab])] -> (DGraph,[DGChange])
globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes [] = 
  if null changes then (dgraph, [])
  -- fällt die alte Kante ganz weg oder wird sie durch ein provenThm ersetzt?
   else ((insEdge provenEdge (delLEdge edge dgraph)),
	    ((DeleteEdge edge):((InsertEdge provenEdge):changes)))

  where
    (GlobalThm _ conservativity) = (dgl_type edgeLab)
    provenEdge = (source,
		  target,
		  DGLink {dgl_morphism = dgl_morphism edgeLab,
			  dgl_type = (GlobalThm True conservativity),
			  dgl_origin = DGProof}
		  )

globDecompForOneEdgeAux dgraph edge@(source,target,edgeLab) changes
 ((node,path):list) =
  globDecompForOneEdgeAux newGraph edge newChanges list

  where
    morphism = case calculateMorphismOfPath (path++(edge:[])) of
                 Just morph -> morph
                 otherwise ->
		   error "globDecomp: could not determine morphism of new edge"
-- ist das die richtige Conservativity??
    (GlobalThm _ conservativity) = (dgl_type edgeLab)
    newEdge = (node,
	       target,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (LocalThm False conservativity),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge dgraph
    newChanges = ((InsertEdge newEdge):changes)


getAllProvenLocGlobPathsTo :: DGraph -> Node -> [LEdge DGLinkLab]
			      -> [(Node, [LEdge DGLinkLab])]
-- ist ein provenLocLink auch schon ein provenLocDefPath??
-- nur Defs suchen oder auch proven Thms?
getAllProvenLocGlobPathsTo dgraph node path =
  globalPaths ++ locGlobPaths ++ 
    (concat (
      [getAllProvenLocGlobPathsTo dgraph (getSourceNode edge) path| 
       (_, path@(edge:edges)) <- globalPaths]))
  

  where
    inEdges = inn dgraph node
    globalEdges = (filter isGlobalDef inEdges) 
		  ++ (filter isProvenGlobalThm inEdges)
    localEdges = (filter isLocalDef inEdges) 
		 ++ (filter isProvenLocalThm inEdges)
    globalPaths = [(getSourceNode edge, (edge:path))| edge <- globalEdges]
    locGlobPaths = [(getSourceNode edge, (edge:path))| edge <- localEdges]

-- applies global subsumption to all unproven global theorem edges if possible
globSubsume ::  ProofStatus -> ProofStatus
globSubsume proofStatus@(globalContext,history,dGraph) =
-- -- ##### überprüfung überflüssig?! #####
  if null (snd nextHistoryElem) then proofStatus  
   else (globalContext, nextHistoryElem:history, nextDGraph)

  where
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dGraph)
    result = globSubsumeAux dGraph ([],[]) globalThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

-- auxiliary function for globSubsume (above)
-- the actual implementation
globSubsumeAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux dGraph historyElement [] = (dGraph, historyElement)
globSubsumeAux dGraph (rules,changes) ((ledge@(source,target,edgeLab)):list) =    if existsDefPathOfMorphismBetween dGraph morphism source target
     then
       globSubsumeAux newGraph (newRules,newChanges) list
     else
       globSubsumeAux dGraph (rules,changes) list
  where
    morphism = dgl_morphism edgeLab
    auxGraph = delLEdge ledge dGraph
    (GlobalThm _ conservativity) = (dgl_type edgeLab)
    newEdge = (source,
	       target,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (GlobalThm True conservativity),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (GlobSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)

{- the same as globSubsume, but for the rule LocSubsumption -}
locSubsume ::  ProofStatus -> ProofStatus
locSubsume proofStatus@(globalContext,history,dGraph) =
  if null (snd nextHistoryElem) then proofStatus  
   else (globalContext, nextHistoryElem:history, nextDGraph)

  where
    localThmEdges = filter isUnprovenLocalThm (labEdges dGraph)
    result = locSubsumeAux dGraph ([],[]) localThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

locSubsumeAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locSubsumeAux dgraph historyElement [] = (dgraph, historyElement)
locSubsumeAux dgraph (rules,changes) ((ledge@(source,target,edgeLab)):list) =
  if existsLocDefPathOfMorphismBetween dgraph morphism source target
     then
       globSubsumeAux newGraph (newRules,newChanges) list
     else
       globSubsumeAux dgraph (rules,changes) list

  where
    morphism = dgl_morphism edgeLab
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity) = (dgl_type edgeLab)
    newEdge = (source,
	       target,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = (LocalThm True conservativity),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (LocSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)

-- checks if there is a path of globalDef edges with the given morphism
-- between the given source and target node
existsDefPathOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
				    -> Bool
existsDefPathOfMorphismBetween dgraph morphism src tgt =
  -- zum Testen: not (null (concat allDefPathsBetween))
  elem morphism filteredMorphismsOfDefPaths

    where
      allDefPathsBetween = getAllDefPathsBetween dgraph src tgt
			     ([]::[LEdge DGLinkLab])
      morphismsOfDefPaths = 
	  map calculateMorphismOfPath allDefPathsBetween
      filteredMorphismsOfDefPaths = getFilteredMorphisms morphismsOfDefPaths 

-- returns all paths of globalDef edges between the given source and target
-- node
getAllDefPathsBetween :: DGraph -> Node -> Node -> [LEdge DGLinkLab]
		           -> [[LEdge DGLinkLab]]
getAllDefPathsBetween dgraph src tgt path =
  [edge:path| edge <- defEdgesFromSrc]
           ++ (concat 
                [getAllDefPathsBetween dgraph src nextTgt (edge:path)|
                (edge,nextTgt) <- nextStep] )

  where
    inGoingEdges = inn dgraph tgt
    globalDefEdges = filter isGlobalDef inGoingEdges
    defEdgesFromSrc = 
	[edge| edge@(source,_,_) <- globalDefEdges, source == src]
    nextStep =
	[(edge, source)| edge@(source,_,_) <- globalDefEdges, source /= src]


existsLocDefPathOfMorphismBetween :: DGraph -> GMorphism -> Node -> Node
                                        -> Bool
existsLocDefPathOfMorphismBetween dgraph morphism src tgt =
  elem morphism filteredMorphismsOfLocDefPaths

    where
      allLocDefPathsBetween = getAllLocDefPathsBetween dgraph src tgt
      morphismsOfLocDefPaths =
	  map calculateMorphismOfPath allLocDefPathsBetween
      filteredMorphismsOfLocDefPaths = 
	  getFilteredMorphisms morphismsOfLocDefPaths

getAllLocDefPathsBetween :: DGraph -> Node -> Node -> [[LEdge DGLinkLab]]
getAllLocDefPathsBetween dgraph src tgt = globDefPaths ++ locGlobDefPaths

  where
    globDefPaths = getAllDefPathsBetween dgraph src tgt ([]::[LEdge DGLinkLab])
    outEdges = out dgraph src
    nextStep = [(edge,getTargetNode edge) | edge <- outEdges]
    pathEnds =
	[(edge,getAllDefPathsBetween dgraph node tgt ([]::[LEdge DGLinkLab]))|
		(edge, node) <- nextStep]
    locGlobDefPaths =
	concat [addEdgeToPaths edge paths | (edge, paths) <- pathEnds]


addEdgeToPaths :: a -> [[a]] -> [[a]]
addEdgeToPaths edge [] = []
addEdgeToPaths edge (path:paths) =
  (edge:path):(addEdgeToPaths edge paths)

{- alle Nachfolger von src holen, die über eine locDef edge zu erreichen sind,
   ab jedem Nachfolger alle defPaths zu tgt holen
   jeweils mit der locDef edge concatinieren
   diese Menge mit der Menge der defPaths zwischen src und tgt zusammentun-}
{-  [map (edge++) (getAllDefPathsBetween nextSrc tgt ([]::[LEdge DGLinkLab])
	     ([]::[[LEdge DGLinkLab]]))|(edge,nextSrc) <- nextStep] 

  where
    outGoingEdges = out dgraph src
    localDefEdges = filter isLocalDef outGoingEdges
    nextStep = [(edge, getTargetNode edge)| edge <- localDefEdges]
-}
-- Reihenfolge der Komposition überprüfen

-- ----------------------------------------
-- determines the morphism of a given path
-- ----------------------------------------
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath [] = error "getMorphismOfPath: empty path"
calculateMorphismOfPath path@((src,tgt,edgeLab):furtherPath) =
  case maybeMorphismOfFurtherPath of
    Nothing -> Nothing
    Just morphismOfFurtherPath ->
		  comp Grothendieck morphism morphismOfFurtherPath

  where
    morphism = dgl_morphism edgeLab
    maybeMorphismOfFurtherPath = calculateMorphismOfPath furtherPath

-- removes the "Nothing"s from a list of Maybe GMorphism
-- returns the remaining elements as plain GMorphisms
getFilteredMorphisms :: [Maybe GMorphism] -> [GMorphism]
getFilteredMorphisms morphisms =
  [morph| (Just morph) <- filter isValidMorphism morphisms]

-- returns if True if the given Maybe GMorphisms is not "Nothing"
isValidMorphism :: Maybe GMorphism -> Bool
isValidMorphism morphism =
  case morphism of
    Nothing -> False
    otherwise -> True


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
    (GlobalThm True _) -> True
    otherwise -> False

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) = 
  case dgl_type edgeLab of
    (GlobalThm False _) -> True
    otherwise -> False

isProvenLocalThm :: LEdge DGLinkLab -> Bool
isProvenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm True _) -> True
    otherwise -> False

isUnprovenLocalThm :: LEdge DGLinkLab -> Bool
isUnprovenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm False _) -> True
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