{-# OPTIONS -cpp #-}

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

--import Debug.Trace

import Data.Dynamic
import Data.List(nub)
import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Common.Lib.Graph
import qualified Common.Lib.Map as Map
import Common.Id
import Common.AS_Annotation
import Syntax.AS_Library
import Syntax.Print_AS_Library 
#ifdef UNI_PACKAGE
import GUI.HTkUtils
#else
import Data.Char(isDigit, digitToInt)

listBox :: String -> [String] -> IO (Maybe Int)
listBox prompt choices = do
   putStrLn prompt
   mapM_ putStrLn $ zipWith (\ n c -> shows n ": " ++ c) [0::Int ..] choices
   putStrLn "Please enter a number on the next line"
   s <- getLine
   if all isDigit s then 
          let n = foldl ( \ r a -> r * 10 + digitToInt a) 0 s in 
              if n >= length choices then
                 putStrLn "number to large, try again"
                 >> listBox prompt choices
              else putStrLn ("you have chosen entry \"" ++ choices!!n)
                   >> return (Just n)
      else putStrLn ("illegal input \"" ++ s ++ "\" try again")
           >> listBox prompt choices
#endif

{-
   proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}

{-type ProofStatus = (GlobalContext,LibEnv,[([DGRule],[DGChange])],DGraph)


umstellen auf:-}

type ProofHistory = [([DGRule],[DGChange])]
type ProofStatus = (LIB_NAME,LibEnv,Map.Map LIB_NAME ProofHistory) 


data DGRule = 
   TheoremHideShift
 | HideTheoremShift (LEdge DGLinkLab)
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
 | LocSubsumption (LEdge DGLinkLab)
 | GlobSubsumption (LEdge DGLinkLab)
 | LocalInference
 | BasicInferendge BasicProof
 | BasicConsInference Edge BasicConsProof
   deriving (Eq, Show)

data DGChange = InsertNode (LNode DGNodeLab)
              | DeleteNode (LNode DGNodeLab)
              | InsertEdge (LEdge DGLinkLab)
              | DeleteEdge (LEdge DGLinkLab)
  deriving (Eq,Show)

data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (Proof_status proof_tree)
     |  Guessed
     |  Conjectured
     |  Handwritten

instance Eq BasicProof where
  Guessed == Guessed = True
  Conjectured == Conjectured = True
  Handwritten == Handwritten = True
  BasicProof lid1 p1 == BasicProof lid2 p2 =
    coerce lid1 lid2 p1 == Just p2

instance Show BasicProof where
  show (BasicProof lid1 p1) = show p1
  show Guessed = "Guessed"
  show Conjectured = "Conjectured"
  show Handwritten = "Handwritten"

data BasicConsProof = BasicConsProof -- more detail to be added ...
     deriving (Eq, Show)

{- todo: implement apply for GlobDecomp and Subsumption 
   the list of DGChage must be constructed in parallel to the
   new DGraph -}
applyRule :: DGRule -> DGraph -> Maybe ([DGChange],DGraph)
applyRule = error "Proofs.hs:applyRule"


automatic :: ProofStatus -> IO ProofStatus
automatic = automaticRecursive 0



automaticRecursive :: Int -> ProofStatus -> IO ProofStatus
automaticRecursive cnt proofStatus = do
  (libname,libEnv,proofHistory) <- automaticAux proofStatus
  proofHistoryAuxList <- blubb cnt (Map.toList proofHistory)
  let newProofHistory = Map.fromList proofHistoryAuxList
  automaticRecursive 1 (libname,libEnv,newProofHistory)


blubb :: Int -> [(LIB_NAME,ProofHistory)] -> IO [(LIB_NAME,ProofHistory)]
blubb _ [] = return []
blubb cnt (history:list) = do
  newHistory <- automaticRecursiveAux cnt history
  newList <- blubb cnt list
  return (newHistory:newList)

automaticRecursiveAux :: Int -> (LIB_NAME,ProofHistory)
		      -> IO (LIB_NAME,ProofHistory)
automaticRecursiveAux cnt (libname,history) = do
  let (newHistoryPart, oldHistory) = splitAt (5+cnt) history
  if (null (concat (map snd (take 5 newHistoryPart)))) && (cnt == 1) then
     return (libname,history)-- ?? - proofStatus
   else do
    let (rules, changes) = concatHistoryElems (reverse newHistoryPart)
	newHistoryElem = (rules, removeContraryChanges changes)
	newHistory = newHistoryElem:oldHistory
    return (libname,newHistory)



{- applies the rules recursively until no further changes can be made -}
{- automaticRecursive :: Int -> ProofStatus -> IO ProofStatus
automaticRecursive cnt proofStatus = do
  (globalContext, libEnv, history, dgraph) <- automaticAux proofStatus
  let (newHistoryPart, oldHistory) = splitAt (5+cnt) history
  if (null (concat (map snd (take 5 newHistoryPart)))) && (cnt == 1) then
     return proofStatus
   else do
    let (rules, changes) = concatHistoryElems (reverse newHistoryPart)
	newHistoryElem = (rules, removeContraryChanges changes)
	newHistory = newHistoryElem:oldHistory
    automaticRecursive 1 (globalContext, libEnv, newHistory, dgraph)
-}

automaticAux :: ProofStatus -> IO ProofStatus
automaticAux p = do
  p1 <- globSubsume p
  p2 <- globDecomp p1
  p3 <- locSubsume p2
  p4 <- locDecomp p3
  hideTheoremShift True p4

concatHistoryElems :: [([DGRule],[DGChange])] -> ([DGRule],[DGChange])
concatHistoryElems [] = ([],[])
concatHistoryElems ((rules,changes):elems) =
  (rules++(fst (concatHistoryElems elems)),changes++(snd (concatHistoryElems elems)))

-- -------------------------------
-- methods used in several proofs
-- -------------------------------
lookupDGraphError :: LIB_NAME -> a
lookupDGraphError libname = error ("Could not find lib with name <" 
				   ++(show libname)++ "> in the given LibEnv")

mkResultProofStatus :: ProofStatus -> DGraph -> ([DGRule],[DGChange]) -> ProofStatus
mkResultProofStatus (libname,libEnv,proofHistory) dgraph historyElem =
  case Map.lookup libname libEnv of
    Nothing -> lookupDGraphError libname
    Just (globalContext,globalAnnos,_) ->
      (libname,
       Map.insert libname (globalContext,globalAnnos,dgraph) libEnv,
       Map.insert libname (historyElem:history) 
                  (prepareResultProofHistory proofHistory))
      
    where
      history = case Map.lookup libname proofHistory of
		  Nothing -> []
		  Just h -> h

{- mkResultProofStatus :: ProofStatus -> DGraph -> ([DGRule],[DGChange]) -> ProofStatus
mkResultProofStatus (libname,libEnv,proofHistory) [] =
  (libname,libEnv,prepareResultProofHistory proofHistory)
mkResultProofStatus (libname,libEnv,proofHistory) 
			((ln,dgraph,historyElem):list) =
  undefined -}


prepareResultProofHistory :: Map.Map LIB_NAME ProofHistory
			  -> Map.Map LIB_NAME ProofHistory
prepareResultProofHistory proofHistory = Map.map (([],[]):) proofHistory


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
globDecomp :: ProofStatus -> IO ProofStatus
globDecomp proofStatus@(libname, libEnv,_) =
  case Map.lookup libname libEnv of
    Nothing -> return proofStatus
    Just (_,_,dgraph) -> do
      let globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
	  (newDGraph, newHistoryElem) 
	      = globDecompAux dgraph globalThmEdges ([],[])
	  (finalDGraph, finalHistoryElem) 
	      = removeSuperfluousInsertions newDGraph newHistoryElem
          newProofStatus = mkResultProofStatus proofStatus finalDGraph finalHistoryElem
      return newProofStatus


{- removes all superfluous insertions from the list of changes as well as
   from the development graph  (i.e. insertions of edges that are
   equivalent to edges or paths resulting from the other insertions) -}
removeSuperfluousInsertions :: DGraph -> ([DGRule],[DGChange])
			         -> (DGraph,([DGRule],[DGChange]))
removeSuperfluousInsertions dgraph (rules,changes)
  = (newDGraph,(rules,newChanges))

  where
    localThms = [edge | (InsertEdge edge) 
		        <- filter isLocalThmInsertion changes]
    (newDGraph, localThmsToInsert)
	= removeSuperfluousEdges dgraph localThms
    newChanges = (filter (not.isLocalThmInsertion) changes)
		     ++ [InsertEdge edge | edge <- localThmsToInsert]



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
  if isRedundant newEdge dgraph changes list
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
globSubsume ::  ProofStatus -> IO ProofStatus
globSubsume proofStatus@(ln,libEnv,_) = do
  let dgraph = lookupDGraph ln proofStatus
      globalThmEdges = filter isUnprovenGlobalThm (labEdges dgraph)
    -- the 'nub' is just a workaround, because some of the edges in the graph
    -- do not differ from each other in this represetation - which causes
    -- problems on deletion
      result = globSubsumeAux libEnv dgraph ([],[]) (nub globalThmEdges)
      nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus 
	  = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus


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
locDecomp ::  ProofStatus -> IO ProofStatus
locDecomp proofStatus@(ln,libEnv,_) = do
  let dgraph = lookupDGraph ln proofStatus
      localThmEdges = filter isUnprovenLocalThm (labEdges dgraph)
      result = locDecompAux libEnv dgraph ([],[]) localThmEdges
      nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus 
	  = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus

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
    th = computeLocalTheory libEnv dgraph src
    pathsWithoutEdgeItself = [path|path <- allPaths, notElem ledge path]
    filteredPaths = filterByTranslation th morphism pathsWithoutEdgeItself
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
      result = locSubsumeAux libEnv dgraph ([],[]) localThmEdges
      nextDGraph = fst result
      nextHistoryElem = snd result
      newProofStatus
	  = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
  return newProofStatus

-- auxiliary method for locSubsume
locSubsumeAux :: LibEnv -> DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
locSubsumeAux libEnv dgraph historyElement [] = (dgraph, historyElement)
locSubsumeAux libEnv dgraph (rules,changes) ((ledge@(src,tgt,edgeLab)):list) =
  case (getDGNode libEnv dgraph tgt, maybeThSrc) of
    (Just (target,_), Just thSrc) ->
      case (maybeResult (computeTheory libEnv dgraph target), maybeResult (translateG_theory morphism thSrc)) of
        (Just theoryTgt, Just (G_theory lidSrc _ sensSrc)) ->
          case maybeResult (coerceTheory lidSrc theoryTgt) of
            Nothing -> locSubsumeAux libEnv dgraph (rules,changes) list
	    Just (_,sentencesTgt) ->
              if (all (`elem` sentencesTgt) sensSrc) 
               then locSubsumeAux libEnv newGraph (newRules,newChanges) list
                else locSubsumeAux libEnv dgraph (rules,changes) list
        otherwise -> locSubsumeAux libEnv dgraph (rules,changes) list
    otherwise -> -- showDiags defaultHetcatsOpts (errSrc++errTgt)
		 locSubsumeAux libEnv dgraph (rules,changes) list

  where
    morphism = dgl_morphism edgeLab
    maybeThSrc = computeLocalTheory libEnv dgraph src
    auxGraph = delLEdge ledge dgraph
    (LocalThm _ conservativity conservStatus) = (dgl_type edgeLab)
    newEdge = (src,
	       tgt,
	       DGLink {dgl_morphism = morphism,
		       dgl_type = 
		         (LocalThm (Proven [])
			  conservativity conservStatus),
		       dgl_origin = DGProof}
               )
    newGraph = insEdge newEdge auxGraph
    newRules = (LocSubsumption ledge):rules
    newChanges = (DeleteEdge ledge):((InsertEdge newEdge):changes)


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
insertNewEdges dgraph changes (edge:edges) =
  if isDuplicate edge dgraph changes then insertNewEdges dgraph changes edges
   else insertNewEdges (insEdge edge dgraph) ((InsertEdge edge):changes) edges


{- creates a new proven HidingThm edge from the given HidingThm edge using the edge list as the proofBasis -}
makeProvenHidingThmEdge :: [LEdge DGLinkLab] -> LEdge DGLinkLab -> LEdge DGLinkLab
makeProvenHidingThmEdge proofBasisEdges (src,tgt,edgeLab) =
  (src,
   tgt,
   DGLink {dgl_morphism = morphism,
	   dgl_type = (HidingThm hidingMorphism 
		       (Proven (map getLabelOfEdge proofBasisEdges))),
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
prettyPrintPath dgraph [] = "<empty path>"
prettyPrintPath dgraph path =
  "(" ++ (prettyPrintNodesOfPath dgraph path) ++ ")"


{- returns the name of the source node of the given edge-}
prettyPrintSourceNode :: DGraph -> LEdge DGLinkLab -> String
prettyPrintSourceNode dgraph (src,_,_) =
   getDGNodeName $ lab' (context src dgraph)


{- returns the name of the target node of the given edge-}
prettyPrintTargetNode :: DGraph -> LEdge DGLinkLab -> String
prettyPrintTargetNode dgraph (_,tgt,_) =
   getDGNodeName $ lab' (context tgt dgraph)


{- creates a unproven global thm edge for the given path, i.e. with the same source and target nodes and the same morphism as the path -}
createEdgeForPath :: [LEdge DGLinkLab] -> LEdge DGLinkLab
createEdgeForPath path =
  case (calculateMorphismOfPath path) of
    Just morphism -> (getSourceNode (head path),
                      getTargetNode (last path),
		      DGLink {dgl_morphism = morphism,
			      dgl_type = (GlobalThm Static.DevGraph.Open None
					  Static.DevGraph.Open),
			      dgl_origin = DGProof}
		     )    
    Nothing -> error ("Could not determine morphism of path " ++ (show path))


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
    otherwise -> Nothing

{- returns the Conservativity if the given edge has one,
   otherwise an error is raised -}
getConservativity :: LEdge DGLinkLab -> Conservativity
getConservativity edge@(_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm _ cons _) -> cons
    (GlobalThm _ cons _) -> cons
    otherwise -> None

-- ----------------------------------------------
-- theorem hide shift
-- ----------------------------------------------

theoremHideShift :: ProofStatus -> IO ProofStatus
theoremHideShift proofStatus@(ln,_,_) = do
  let dgraph = lookupDGraph ln proofStatus
      allNodes = nodes dgraph
      (nonLeaves,leaves) 
	  = splitByProperty allNodes (hasIngoingHidingDef dgraph)
  auxProofstatus <- handleLeaves (prepareProofStatus proofStatus) leaves
  finalProofstatus <- handleNonLeaves auxProofstatus nonLeaves
  return (reviseProofStatus finalProofstatus)


prepareProofStatus :: ProofStatus -> ProofStatus
prepareProofStatus (ln,libEnv,history) = 
  (ln,libEnv,Map.map prepareHistory history)

prepareHistory :: [([DGRule],[DGChange])] -> [([DGRule],[DGChange])]
prepareHistory [] = [([],[])]
prepareHistory history@((_,[]):_) = history
prepareHistory history = ([],[]):history

reviseProofStatus :: ProofStatus -> ProofStatus
reviseProofStatus proofstatus@(ln,libEnv,historyMap) =
  (ln, libEnv, Map.map reviseHistory historyMap)

reviseHistory :: ProofHistory -> ProofHistory
reviseHistory [] = []
reviseHistory ((_,changes):history) =
  ([TheoremHideShift],(removeContraryChanges changes)):history

showChanges :: [DGChange] -> String
showChanges [] = ""
showChanges (change:changes) = 
  case change of
    InsertEdge edge -> "InsertEdge " ++ (showEdgeChange edge)
		       ++ (showChanges changes)
    DeleteEdge edge -> "DeleteEdge " ++ (showEdgeChange edge)
		       ++ (showChanges changes)
    InsertNode node -> "InsertNode " ++ (showNodeChange node)
		       ++ (showChanges changes)
    DeleteNode node -> "DeleteNode " ++ (showNodeChange node)
		       ++ (showChanges changes)

showEdgeChange :: LEdge DGLinkLab -> String
showEdgeChange (src,tgt,edgelab) =
  " from " ++ (show src) ++ " to " ++ (show tgt) ++ " and of type " ++ (show (dgl_type edgelab)) ++ "\n\n"

showNodeChange :: LNode DGNodeLab -> String
showNodeChange (descr, nodelab) =
  (show descr) ++ " with name " ++ (show (dgn_name nodelab)) ++ "\n\n"


splitByProperty :: [a] -> (a -> Bool) -> ([a],[a])
splitByProperty [] _ = ([],[])
splitByProperty (x:xs) f =
  if (f x) then (x:first, second) else (first, x:second)
  where
    next = splitByProperty xs f
    first = fst next
    second = snd next


hasIngoingHidingDef :: DGraph -> Node -> Bool
hasIngoingHidingDef dgraph node =
  not (null hidingDefEdges) || or (map (hasIngoingHidingDef dgraph) next)
  where
    inGoingEdges = inn dgraph node
    hidingDefEdges = filter isHidingDef inGoingEdges
    globalDefEdges = filter isGlobalDef inGoingEdges
    next = map getSourceNode globalDefEdges


handleLeaves :: ProofStatus -> [Node] -> IO ProofStatus
handleLeaves proofstatus [] = return proofstatus
handleLeaves proofstatus (node:list) = do
  auxProofstatus <- convertToNf proofstatus node
  handleLeaves auxProofstatus list


lookupGlobalContext :: LIB_NAME -> ProofStatus -> GlobalContext
lookupGlobalContext ln (_,libEnv,_) =
  case Map.lookup ln libEnv of
    Nothing -> lookupDGraphError ln
    Just globalContext -> globalContext

lookupDGraph :: LIB_NAME -> ProofStatus -> DGraph
lookupDGraph ln proofstatus = dgraph
  where
    (_,_,dgraph) = lookupGlobalContext ln proofstatus

lookupHistory :: LIB_NAME -> ProofStatus -> ProofHistory
lookupHistory ln (_,_,historyMap) =
  case Map.lookup ln historyMap of
    Nothing -> []
    Just history -> history

updateHistory :: LIB_NAME -> [DGChange] -> ProofStatus -> ProofStatus
updateHistory ln changes proofstatus@(l,libEnv,historyMap) =
  (l, libEnv,
  Map.insert ln (addChanges changes (lookupHistory ln proofstatus)) historyMap)

updateLibEnv :: LIB_NAME -> DGraph -> ProofStatus -> ProofStatus
updateLibEnv ln dgraph proofstatus@(l,libEnv,historyMap) =
  (l,
   Map.insert ln 
   (updateDGraphInGlobalContext dgraph (lookupGlobalContext ln proofstatus))
   libEnv,
   historyMap)

updateProofStatus :: LIB_NAME -> DGraph -> [DGChange] -> ProofStatus 
		  -> ProofStatus
updateProofStatus ln dgraph changes proofstatus =
  updateHistory ln changes proofstatusAux
  where
    proofstatusAux = updateLibEnv ln dgraph proofstatus

updateDGraphInGlobalContext :: DGraph -> GlobalContext -> GlobalContext
updateDGraphInGlobalContext dgraph (gAnnos,gEnv,_) = (gAnnos,gEnv,dgraph)


convertToNf :: ProofStatus -> Node -> IO ProofStatus
convertToNf proofstatus@(ln,libEnv,history) node = do
  let dgraph = lookupDGraph ln proofstatus
      nodelab = lab' (context node dgraph)
      [newNode] = newNodes 0 dgraph
      newDgnode = case isDGRef nodelab of
		    False -> mkNfDGNode newNode nodelab
		    True -> mkNfDGRef newNode nodelab
      auxGraph = insNode newDgnode dgraph
  (finalGraph,changes) <- adoptEdges auxGraph node newNode
  let finalChanges =  [InsertNode newDgnode] ++ changes
		      ++ [DeleteNode (node,nodelab)]
  return (updateProofStatus ln finalGraph finalChanges proofstatus)
  where 
    mkNfDGNode :: Node -> DGNodeLab -> LNode DGNodeLab
    mkNfDGNode newNode nodelab = 
	(newNode,
	 DGNode {dgn_name = dgn_name nodelab,
		 dgn_sign = dgn_sign nodelab,
		 dgn_sens = dgn_sens nodelab,
		 dgn_nf = Just newNode,
		 dgn_sigma = Just (ide Grothendieck (dgn_sign nodelab)),
		 dgn_origin = DGProof
		})
    mkNfDGRef :: Node -> DGNodeLab -> LNode DGNodeLab
    mkNfDGRef newNode nodelab =
	(newNode,
	 DGRef {dgn_renamed = dgn_renamed nodelab,
		dgn_libname = dgn_libname nodelab,
		dgn_node = dgn_node nodelab, -- nf im refGraph finden
		dgn_nf = Just newNode,
		dgn_sigma = Nothing -- Just (ide Grothendieck sign)
	       })

mkNfNode :: DGraph -> Node -> Node -> ProofStatus
	    -> IO (ProofStatus,LNode DGNodeLab)
mkNfNode dgraph node newNode proofstatus = do
  let nodelab = lab' (context node dgraph)
  case isDGRef nodelab of
    True -> mkDGRefNfNode dgraph nodelab newNode proofstatus
    False -> mkDGNodeNfNode dgraph nodelab newNode proofstatus


mkDGNodeNfNode :: DGraph -> DGNodeLab -> Node -> ProofStatus
	       -> IO (ProofStatus,LNode DGNodeLab)
mkDGNodeNfNode dgraph nodelab newNode proofstatus = do
  let lnode = (newNode,
	 DGNode {dgn_name = dgn_name nodelab,
		 dgn_sign = dgn_sign nodelab,
		 dgn_sens = dgn_sens nodelab,
		 dgn_nf = Just newNode,
		 dgn_sigma = Just (ide Grothendieck (dgn_sign nodelab)),
		 dgn_origin = DGProof
		})
  return (proofstatus,lnode)

mkDGRefNfNode :: DGraph -> DGNodeLab -> Node -> ProofStatus
	      -> IO (ProofStatus,(LNode DGNodeLab))
mkDGRefNfNode dgraph nodelab newNode proofstatus@(ln,_,_) = do
  auxProofstatus <- theoremHideShift 
		    (changeCurrentLibName (dgn_libname nodelab) proofstatus)
  let refGraph = lookupDGraph (dgn_libname nodelab) proofstatus
      (Just refNf) = dgn_nf (lab' (context (dgn_node nodelab) refGraph))
  let lnode = (newNode,
	       DGRef {dgn_renamed = dgn_renamed nodelab,
		      dgn_libname = dgn_libname nodelab,
		      dgn_node = refNf,
		      dgn_nf = Just newNode,
		      dgn_sigma = Nothing -- Just (ide Grothendieck sign)
		     })
  return (changeCurrentLibName ln auxProofstatus,lnode)


changeCurrentLibName :: LIB_NAME -> ProofStatus -> ProofStatus
changeCurrentLibName ln (_,libEnv,historyMap) = (ln,libEnv,historyMap)

addChanges :: [DGChange] -> [([DGRule],[DGChange])] -> [([DGRule],[DGChange])]
addChanges changes [] = [([],changes)]
addChanges changes (hElem:history) = (fst hElem, (snd hElem)++changes):history


adoptEdges :: DGraph -> Node -> Node -> IO (DGraph,[DGChange])
adoptEdges dgraph oldNode newNode = do
  let ingoingEdges = inn dgraph oldNode
      outgoingEdges = [outEdge| outEdge <- out dgraph oldNode,
		                not (elem outEdge ingoingEdges)]
      (auxGraph, changes) = adoptEdgesAux dgraph ingoingEdges newNode True
      (finalGraph, furtherChanges) 
	  = adoptEdgesAux auxGraph outgoingEdges newNode False
  return (finalGraph, changes ++ furtherChanges)


adoptEdgesAux :: DGraph -> [LEdge DGLinkLab] -> Node -> Bool
		     -> (DGraph,[DGChange])
adoptEdgesAux dgraph [] _ _ = (dgraph,[])
adoptEdgesAux dgraph (oldEdge@(src,tgt,edgelab):list) node areIngoingEdges =
  (finalGraph, [DeleteEdge oldEdge,InsertEdge newEdge]++furtherChanges)

  where
    (newSrc,newTgt) = if src == tgt then (node,node) else (src,tgt)
    newEdge = if areIngoingEdges then (newSrc,node,edgelab)
	        else (node,newTgt,edgelab)
    auxGraph = insEdge newEdge (delLEdge oldEdge dgraph)
    (finalGraph,furtherChanges) 
	= adoptEdgesAux auxGraph list node areIngoingEdges

-- was machen, wenn der Knoten ein DGRef ist??
handleNonLeaves :: ProofStatus -> [Node] -> IO ProofStatus
handleNonLeaves proofstatus [] = return proofstatus
handleNonLeaves proofstatus@(ln,_,_) (node:list) = do
  let dgraph = lookupDGraph ln proofstatus
      nodelab = lab' (context node dgraph)
  case dgn_nf nodelab of
    Just _ -> handleNonLeaves proofstatus list
    Nothing -> do
      auxProofstatus <- createNfsForPredecessors proofstatus node
      let auxGraph = lookupDGraph ln auxProofstatus
          newDefInEdges = [edge| edge <- inn auxGraph node,
			  isGlobalDef edge || isHidingDef edge]
          newPredecessors = [src| (src,_,_) <- newDefInEdges]
          diagram = makeDiagram auxGraph (node:newPredecessors) newDefInEdges
          Result diags res = gWeaklyAmalgamableCocone diagram
      case res of
        Nothing -> do sequence $ map (putStrLn . show) diags
		      handleNonLeaves auxProofstatus list
        Just (sign,map) -> do
          let [nfNode] = newNodes 0 auxGraph
              nfDGNode = case isDGRef nodelab of
			   False -> mkNfDGNode nfNode nodelab (dgn_sign nodelab) -- actually sign
			   True -> mkNfDGRef nfNode nodelab sign

          (auxGraph', changes) <- 
	      setNfOfNode (insNode nfDGNode auxGraph) node nfNode
          let (finalGraph,changes') = insertEdgesToNf auxGraph' nfNode map
              finalProofstatus = updateProofStatus ln finalGraph 
				([InsertNode nfDGNode] ++ changes
				 ++ changes') auxProofstatus
          handleNonLeaves finalProofstatus list
	  
  where
    mkNfDGNode :: Node -> DGNodeLab -> G_sign -> LNode DGNodeLab
    mkNfDGNode newNode nodelab sign =
	(newNode, 
	 DGNode {dgn_name = dgn_name nodelab,
		 dgn_sign = sign,
		 dgn_sens = dgn_sens nodelab,
		 dgn_nf = Just newNode,
		 dgn_sigma = dgn_sigma nodelab,
		 dgn_origin = DGProof
		})
    mkNfDGRef :: Node -> DGNodeLab -> G_sign -> LNode DGNodeLab
    mkNfDGRef newNode nodelab sign =
	(newNode,
	 DGRef {dgn_renamed = dgn_renamed nodelab,
		dgn_libname = dgn_libname nodelab,
		dgn_node = dgn_node nodelab,  -- nf im refGraph finden
		dgn_nf = Just newNode,
		dgn_sigma = dgn_sigma nodelab -- so richtig?
	       })

createNfsForPredecessors :: ProofStatus -> Node -> IO ProofStatus
createNfsForPredecessors proofstatus@(ln,_,_) node = do
  handleNonLeaves proofstatus predecessors

  where
    dgraph = lookupDGraph ln proofstatus
    defInEdges =  [edge| edge@(src,_,_) <- inn dgraph node,
		   (isGlobalDef edge || isHidingDef edge) 
		   && node /= src]
    predecessors = [src| (src,_,_) <- defInEdges]


insertEdgesToNf :: DGraph -> Node -> (Map.Map Node GMorphism)
		   -> (DGraph,[DGChange])
insertEdgesToNf dgraph nfNode map =
    insertEdgesToNfAux  dgraph nfNode (Map.toList map)
    
insertEdgesToNfAux :: DGraph -> Node -> [(Node,GMorphism)] 
		   -> (DGraph,[DGChange])
insertEdgesToNfAux dgraph _ [] = (dgraph,[])
insertEdgesToNfAux dgraph nfNode ((node,morph):list) =
  (finalGraph, (InsertEdge ledge):changes)

  where
    ledge = (node, nfNode, DGLink {dgl_morphism = morph,
				   dgl_type = GlobalDef,
				   dgl_origin = DGProof
				  })    
    auxGraph = insEdge ledge dgraph
    (finalGraph,changes) = insertEdgesToNfAux auxGraph nfNode list

-- was machen, wenn der Knoten ein DGRef ist??
setNfOfNode :: DGraph -> Node -> Node -> IO (DGraph,[DGChange])
setNfOfNode dgraph node nf_node = do
  (finalGraph,changes) <- adoptEdges auxGraph node newNode
  return (delNode node finalGraph,
	  ((InsertNode newDgNode):changes)++[DeleteNode oldDgNode])

  where
    nodeLab = lab' (context node dgraph)
    oldDgNode = labNode' (context node dgraph)
    [newNode] = newNodes 0 dgraph
    newDgNode = (newNode, DGNode {dgn_name = dgn_name nodeLab,
				  dgn_sign = dgn_sign nodeLab,
				  dgn_sens = dgn_sens nodeLab,
				  dgn_nf = Just nf_node,
				  dgn_sigma = dgn_sigma nodeLab,
				  dgn_origin = DGProof
				 })
    auxGraph = insNode newDgNode dgraph


makeDiagram :: DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagram = makeDiagramAux empty

makeDiagramAux :: GDiagram -> DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagramAux diagram _ [] [] = diagram
makeDiagramAux diagram dgraph [] (edge@(src,tgt,lab):list) =
  makeDiagramAux (insEdge morphEdge diagram) dgraph [] list
    where morphEdge = if isHidingDef edge then (tgt,src,dgl_morphism lab) 
		       else (src,tgt,dgl_morphism lab)
makeDiagramAux diagram dgraph (node:list) edges =
  makeDiagramAux (insNode sigNode diagram) dgraph list edges
    where sigNode = (node, dgn_sign (lab' (context node dgraph)))

-- ----------------------------------------------
-- methods that keep the change list clean
-- ----------------------------------------------

removeContraryChanges :: [DGChange] -> [DGChange]
removeContraryChanges [] = []
removeContraryChanges (change:changes) =
  if elem contraryChange changes
   then removeContraryChanges (removeChange contraryChange changes)
    else change:(removeContraryChanges changes)
  where
    contraryChange = getContraryChange change


getContraryChange :: DGChange -> DGChange
getContraryChange change =
  case change of
    InsertEdge edge -> DeleteEdge edge
    DeleteEdge edge -> InsertEdge edge
    InsertNode node -> DeleteNode node
    DeleteNode node -> InsertNode node


removeChange :: DGChange -> [DGChange] -> [DGChange]
removeChange change changes =
  (takeWhile (change /=) changes)
  ++(tail (dropWhile (change /=) changes))


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


getAllPathsBeginningWithHidingDefTo :: DGraph -> Node -> [LEdge DGLinkLab]
				    -> [(Node, [LEdge DGLinkLab])]
getAllPathsBeginningWithHidingDefTo dgraph node path =
  resultPath ++ 
  (concat ( [getAllPathsBeginningWithHidingDefTo
             dgraph (getSourceNode edge) (edge:path) | 
	     edge <- nextEdges]))
  where
    inEdges = inn dgraph node
    nextEdges = [edge| edge <- inEdges, not (elem edge path)]
    resultPath = 
      if ((not (null path)) && (isHidingDef (head path)))
	 then [(node,path)] else []



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

{-
getAllPathsFrom :: DGraph -> Node -> [[LEdge DGLinkLab]]
getAllPathsFrom = getAllPathsFromAux []

getAllPathsFromAux :: [LEdge DGLinkLab] -> DGraph -> Node
		   -> [[LEdge DGLinkLab]]
getAllPathsFromAux path dgraph src =
  [path ++ [edge]| edge <- edgesFromSrc, notElem edge path]
    ++(concat
        [getAllPathsFromAux (path ++ [edge]) dgraph nextSrc| 
	 (edge,nextSrc) <- nextStep])

  where
    edgesFromSrc = out dgraph src
    nextStep = [(edge,tgt)| edge@(_,tgt,_) <- edgesFromSrc,
		tgt /= src && notElem edge path] -}

getAllPathsOfTypeFrom :: DGraph -> Node -> (LEdge DGLinkLab -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFrom = getAllPathsOfTypeFromAux []


getAllPathsOfTypeFromAux :: [LEdge DGLinkLab] -> DGraph -> Node 
			 -> (LEdge DGLinkLab -> Bool) -> [[LEdge DGLinkLab]]
getAllPathsOfTypeFromAux path dgraph src isType = 
  [path ++ [edge]| edge <- edgesFromSrc, notElem edge path && isType edge]
    ++(concat
        [getAllPathsOfTypeFromAux (path ++ [edge]) dgraph nextSrc isType| 
	 (edge,nextSrc) <- nextStep])

  where
    edgesFromSrc = out dgraph src
    nextStep = [(edge,tgt)| edge@(_,tgt,_) <- edgesFromSrc,
		tgt /= src && notElem edge path && isType edge] 

-- -------------------------------------
-- methods to check the type of an edge
-- -------------------------------------
isProven :: LEdge DGLinkLab -> Bool
isProven edge = isGlobalDef edge || isLocalDef edge 
		|| isProvenGlobalThm edge || isProvenLocalThm edge
                || isProvenHidingThm edge

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
    _ -> False

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) = 
  case dgl_type edgeLab of
    (GlobalThm Static.DevGraph.Open _ _) -> True
    _ -> False

isProvenLocalThm :: LEdge DGLinkLab -> Bool
isProvenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm (Proven _) _ _) -> True
    _ -> False

isUnprovenLocalThm :: LEdge DGLinkLab -> Bool
isUnprovenLocalThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (LocalThm (Static.DevGraph.Open) _ _) -> True
    _ -> False


isHidingEdge :: LEdge DGLinkLab -> Bool
isHidingEdge edge = isHidingDef edge || isHidingThm edge

isHidingDef :: LEdge DGLinkLab -> Bool
isHidingDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    HidingDef -> True
    _ -> False

isHidingThm :: LEdge DGLinkLab -> Bool
isHidingThm edge = isProvenHidingThm edge || isUnprovenHidingThm edge


isProvenHidingThm :: LEdge DGLinkLab -> Bool
isProvenHidingThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (HidingThm _ (Proven _)) -> True
    _ -> False

isUnprovenHidingThm :: LEdge DGLinkLab -> Bool
isUnprovenHidingThm (_,_,edgeLab) =
  case dgl_type edgeLab of
    (HidingThm _ Static.DevGraph.Open) -> True
    _ -> False

-- ----------------------------------------------------------------------------
-- other methods on edges
-- ----------------------------------------------------------------------------
{- returns true, if an identical edge is already in the graph or marked to be inserted,
 false otherwise-}
isDuplicate :: LEdge DGLinkLab -> DGraph -> [DGChange] -> Bool
isDuplicate newEdge dgraph changes = 
  elem (InsertEdge newEdge) changes || elem newEdge (labEdges dgraph)

{- returns true, if the given edge is duplicate or
 if there already exists a parallel path,
 which starts with a localThmEdge to one of the startnodes in 'otherNewEdge'
 and has the same morphism as the given edge,
 false otherwise -}
isRedundant :: LEdge DGLinkLab -> DGraph -> [DGChange] 
              ->[(Node, [LEdge DGLinkLab])] -> Bool
isRedundant newEdge@(src,_,label) dgraph changes otherNewEdges =
  isDuplicate newEdge dgraph changes 
  || elem (Just (dgl_morphism label)) morphismsOfParallelPaths

  where
    localThmEdgesToOtherSources = 
      [outEdge|outEdge@(_,tgt,_) <- out dgraph src,
               elem tgt (map fst otherNewEdges)
               && isLocalThm outEdge]
    parallelPaths 
      = concat (map (combineSucceedingEdges otherNewEdges)
                    localThmEdgesToOtherSources)
    morphismsOfParallelPaths = map calculateMorphismOfPath parallelPaths

{- combines the given edge with each of those given paths that start
 with the target node of the edge-}
combineSucceedingEdges :: [(Node,[LEdge DGLinkLab])] -> LEdge DGLinkLab
                          -> [[LEdge DGLinkLab]]
combineSucceedingEdges [] _ = []
combineSucceedingEdges ((src,path):paths) edge@(_,tgt,_) =
  if tgt == src 
   then ((edge:path)):(combineSucceedingEdges paths edge)
   else combineSucceedingEdges paths edge

  
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


-- ---------------------------------------------------------------------------
-- methods for the extension of globDecomp (avoid insertion ofredundant edges)
-- ---------------------------------------------------------------------------

{- returns all paths consisting of local theorem links whose src and tgt nodes
   are contained in the given list of nodes -}
localThmPathsBetweenNodes ::  DGraph -> [Node] -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodes _ [] = []
localThmPathsBetweenNodes dgraph nodes@(x:xs) =
  localThmPathsBetweenNodesAux dgraph nodes nodes

{- auxiliary method for localThmPathsBetweenNodes -}
localThmPathsBetweenNodesAux :: DGraph -> [Node] -> [Node] -> [[LEdge DGLinkLab]]
localThmPathsBetweenNodesAux _ [] _ = []
localThmPathsBetweenNodesAux dgraph (node:srcNodes) tgtNodes =
  (concat (map (getAllPathsOfTypeBetween dgraph isUnprovenLocalThm node) tgtNodes))
  ++ (localThmPathsBetweenNodesAux dgraph srcNodes tgtNodes)

{- combines each of the given paths with matching edges from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
combinePathsWithEdges :: [[LEdge DGLinkLab]] -> [LEdge DGLinkLab]
		     -> [[LEdge DGLinkLab]]
combinePathsWithEdges paths edges =
  concat (map (combinePathsWithEdge paths) edges)

{- combines the given path with each matching edge from the given list
   (i.e. every edge that has as its source node the tgt node of the path)-}
combinePathsWithEdge :: [[LEdge DGLinkLab]] -> LEdge DGLinkLab
		     -> [[LEdge DGLinkLab]]
combinePathsWithEdge [] _ = []
combinePathsWithEdge (path:paths) edge@(src,_,_) =
  case path of
    [] -> combinePathsWithEdge paths edge
    (x:xs) -> if (getTargetNode (last path)) == src 
	      then (path++[edge]):(combinePathsWithEdge paths edge)
		else combinePathsWithEdge paths edge

{- todo: choose a better name for this method...
   returns for each of the given paths a pair consisting of the last edge
   contained in the path and - as a triple - the src, tgt and morphism of the
   complete path
   if there is an empty path in the given list or the morphsim cannot be
   calculated, it is simply ignored -}
calculateResultingEdges :: [[LEdge DGLinkLab]] -> [(LEdge DGLinkLab,(Node,Node,GMorphism))]
calculateResultingEdges [] = []
calculateResultingEdges (path:paths) =
  case path of
    [] -> calculateResultingEdges paths
    (x:xs) ->
       case calculateMorphismOfPath path of
         Nothing -> calculateResultingEdges paths
         Just morphism -> (last path, (src,tgt,morphism)):(calculateResultingEdges paths)

  where src = getSourceNode (head path)
        tgt = getTargetNode (last path)

{- removes from the given list every edge for which there is already an
   equivalent edge or path (i.e. an edge or path with the same src, tgt and
   morphsim) -}
removeSuperfluousEdges :: DGraph -> [LEdge DGLinkLab]
		       -> (DGraph,[LEdge DGLinkLab])
removeSuperfluousEdges dgraph [] = (dgraph,[])
removeSuperfluousEdges dgraph edges
  = removeSuperfluousEdgesAux dgraph edges 
        (calculateResultingEdges combinedPaths) []

  where
    localThmPaths
	= localThmPathsBetweenNodes dgraph (map (getSourceNode) edges)
    combinedPaths = combinePathsWithEdges localThmPaths edges

{- auxiliary method for removeSuperfluousEdges -}
removeSuperfluousEdgesAux :: DGraph -> [LEdge DGLinkLab] 
			  -> [(LEdge DGLinkLab,(Node,Node,GMorphism))] 
			  -> [LEdge DGLinkLab] -> (DGraph,[LEdge DGLinkLab])
removeSuperfluousEdgesAux dgraph [] _ edgesToInsert= (dgraph,edgesToInsert)
removeSuperfluousEdgesAux dgraph ((src,tgt,lab):edges) 
			  resultingEdges edgesToInsert =
  if not (null equivalentEdges)
     then removeSuperfluousEdgesAux
	  newDGraph edges newResultingEdges edgesToInsert
      else removeSuperfluousEdgesAux
	   dgraph edges resultingEdges ((src,tgt,lab):edgesToInsert)

  where 
    equivalentEdges 
	= [e | e <- resultingEdges,(snd e) == (src,tgt,dgl_morphism lab)]
    newResultingEdges = [e | e <- resultingEdges,(fst e) /= (src,tgt,lab)]
    newDGraph = delLEdge (src,tgt,lab) dgraph

{- returns true, if the given change is an insertion of an local theorem edge,
   false otherwise -}
isLocalThmInsertion :: DGChange -> Bool
isLocalThmInsertion change
  = case change of
      InsertEdge edge -> isLocalThm edge
      otherwise -> False

-- --------------------------------------------------------
-- further methods
-- -------------------------------------------------------

-- | Calculate the morphism of a path with given start node
calculateMorphismOfPathWithStart :: DGraph -> LibEnv 
                                    -> (Node,[LEdge DGLinkLab]) 
                                           -> Maybe GMorphism
calculateMorphismOfPathWithStart dg libEnv (n,[]) = do
  ctx <- fst $ match n dg
  case getDGNode libEnv dg (fst (labNode' ctx)) of
    Just dgNode_ctx -> return $ ide Grothendieck (dgn_sign (snd (dgNode_ctx))) -- ??? to simplistic 
    Nothing -> Nothing
  
calculateMorphismOfPathWithStart _ _ (_,p) = calculateMorphismOfPath p

-- ---------------
-- basic inference
-- ---------------

getGoals :: LibEnv -> DGraph -> LEdge DGLinkLab -> Result G_l_sentence_list
getGoals libEnv dg (n,_,edge) = do
  th <- maybeToMonad ("Could node find node "++show n)
              $  computeLocalTheory libEnv dg n
  let mor = dgl_morphism edge
  fmap sensOf $ translateG_theory mor th

getProvers :: Bool -> LogicGraph -> G_sublogics -> [(G_prover,AnyComorphism)]
getProvers consCheck lg gsub =
  if consCheck then
     [(G_cons_checker (targetLogic cid) p,Comorphism cid) | 
        Comorphism cid <- cms,
        p <- cons_checkers (targetLogic cid)]
     else
     [(G_prover (targetLogic cid) p,Comorphism cid) | 
        Comorphism cid <- cms,
        p <- provers (targetLogic cid)]
  where cms = findComorphismPaths lg gsub


selectProver :: [(G_prover,AnyComorphism)] -> IOResult (G_prover,AnyComorphism)
selectProver [p] = return p
selectProver [] = resToIORes $ fatal_error "No pover available" nullPos
selectProver provers = do
   sel <- ioToIORes $ listBox 
                "Choose a translation to a prover-supported logic"
                (map (show.snd) provers)
   i <- case sel of
           Just j -> return j
           _ -> resToIORes $ fatal_error "Proofs.Proofs: selection" nullPos
   return (provers!!i)
 
-- applies basic inference to a given node
basicInferenceNode :: Bool -> LogicGraph -> (LIB_NAME,Node) -> ProofStatus 
                          -> IO (Result ProofStatus)
basicInferenceNode checkCons lg (ln,node) 
         proofStatus@(libname,libEnv,proofHistory) = do
      let dGraph = lookupDGraph libname proofStatus
      ioresToIO (do 
        -- compute the theory of the node, and its name
        G_theory lid1 sign axs <- 
             resToIORes $ computeTheory libEnv dGraph node
        ctx <- resToIORes 
                    $ maybeToMonad ("Could node find node "++show node)
                    $ fst $ match node dGraph
        let nlab = lab' ctx  
            nodeName = case nlab of
              DGNode _ _ _ _ _ _-> dgn_name nlab
              DGRef _ _ _ _ _ -> dgn_renamed nlab
            thName = showPretty (getLIB_ID ln) "_"
                     ++ {-maybe (show node)-} showName nodeName
        -- compute the list of proof goals
        let inEdges = inn dGraph node
            localEdges = filter isUnprovenLocalThm inEdges
        goalslist <- if checkCons then return []
                      else resToIORes $ mapM (getGoals libEnv dGraph) localEdges
        G_l_sentence_list lid3 goals <- 
          if null goalslist then return $ G_l_sentence_list lid1 [] 
            else resToIORes (maybeToMonad 
                                      "Logic mismatch for proof goals" 
                                       (flatG_l_sentence_list goalslist))
        goals1 <- coerce lid1 lid3 goals
        -- select a suitable translation and prover
        let provers = getProvers checkCons lg $ sublogicOfTh $ 
                                (G_theory lid1 sign (axs++goals1))
        (prover,Comorphism cid) <- selectProver provers
        -- Borrowing: translate theory
        let lidS = sourceLogic cid
            lidT = targetLogic cid
        sign' <- coerce lidS lid1 sign
        axs' <- coerce lidS lid1 axs
        (sign'',sens'') <- resToIORes $ map_theory cid (sign',axs')
        case prover of
         G_prover lid4 p -> do
           -- Borrowing: translate goal
           goals' <- coerce lidS lid3 goals
           goals'' <- resToIORes $ mapM (mapNamedM $ map_sentence cid sign') goals'
           -- call the prover
           p' <- coerce lidT lid4 p
           ps <- ioToIORes $ prove p' thName (sign'',sens'') goals'' 
           -- update the development graph
           let (nextDGraph, nextHistoryElem) = proveLocalEdges dGraph localEdges
	       newProofStatus
		 = mkResultProofStatus proofStatus nextDGraph nextHistoryElem
           return newProofStatus
         G_cons_checker lid4 p -> do
           incl <- resToIORes $ inclusion lidT (empty_signature lidT) sign''
           let mor = TheoryMorphism { t_source = empty_theory lidT, 
                                      t_target = (sign'',sens''),
                                      t_morphism = incl } 
           p' <- coerce lidT lid4 p
           ps <- ioToIORes $ cons_check p' thName mor
           let nextHistoryElem = ([LocalInference],[])
             -- ??? to be implemented
               newProofStatus
		 = mkResultProofStatus proofStatus dGraph nextHistoryElem
           return newProofStatus
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
