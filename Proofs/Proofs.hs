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
globDecomp = undefined

{- try to apply rules GlobSubsumption  
     to all global theorem links in the current DG 
   current DG = DGm
   add to proof status the pair ([Subsumption e1,...,Subsumption en],DGm+1)
   where e1...en are those global theorem links in DGm for which the
     rule subsumption can be applied
   if n=0, then just return the original proof status
   DGm+1 results from DGm by application of GlobDecomp e1,...,GlobDecomp en -}
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

globSubsumeAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux dGraph historyElement [] = (dGraph, historyElement)
globSubsumeAux dGraph (rules,changes) ((ledge@(source,target,edgeLab)):list) =    if existsDefPathOfSameMorphism dGraph morphism source target
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
    newChanges = (InsertEdge newEdge):((DeleteEdge ledge):changes)


existsDefPathOfSameMorphism :: DGraph -> GMorphism -> Node -> Node -> Bool
existsDefPathOfSameMorphism dgraph morphism src tgt =
 True 

 -- existsDefPathOfSameMorphismAux dgraph morphism tgt [] src

existsDefPathOfSameMorphismAux dgraph morphism tgt path src =
  if null outGoingEdges then False
   else
     if elem morphism morphismsOfPathsToTgt then True
      else or [existsDefPathOfSameMorphismAux dgraph morphism tgt
	       ((fst step):path) (snd step)| step <- nextStep]

  where 
    outGoingEdges = out dgraph src
    globalDefEdges = filter isGlobalDef outGoingEdges
    nextStep = [(edge, getTargetNode edge)| edge <- globalDefEdges]
    defEdgesToTgt = [edge| edge <- globalDefEdges, tgt == getTargetNode edge]
    defPathsToTgt = [edge:path| edge <- defEdgesToTgt]
    morphismsOfPathsToTgt = map getMorphismOfPath defPathsToTgt

getMorphismOfPath :: [LEdge DGLinkLab] -> GMorphism
getMorphismOfPath [] = error "getMorphismOfPath: empty path"
getMorphismOfPath path@((src,tgt,edgeLab):furtherPath) =
  calculateCombinedMorphism morphism morphismOfFurtherPath

  where
    morphism = dgl_morphism edgeLab
    morphismOfFurtherPath = getMorphismOfPath furtherPath

calculateCombinedMorphism :: GMorphism -> GMorphism -> GMorphism
calculateCombinedMorphism morph1 morph2 = 
  case comp Grothendieck morph1 morph2 of
    Just morphism -> morphism
    Nothing -> error "wie soll mit diesem Fall umgegangen werden?"

getTargetNode :: LEdge DGLinkLab -> Node
getTargetNode (_,target,_) = target

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) = 
  case dgl_type edgeLab of
    (GlobalThm False _) -> True
    otherwise -> False

isGlobalDef ::LEdge DGLinkLab -> Bool
isGlobalDef (_,_,edgeLab) =
  case dgl_type edgeLab of
    GlobalDef -> True
    otherwise -> False

{- the same as globSubsume, but for the rule LocSubsumption -}
locSubsume ::  ProofStatus -> ProofStatus
locSubsume = undefined
