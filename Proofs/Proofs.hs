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
  if null (snd nextHistoryElem) then proofStatus  
   else (globalContext, nextHistoryElem:history, nextDGraph)

  where
    globalThmEdges = filter isUnprovenGlobalThm (labEdges dGraph)
    result = globSubsumeAux dGraph ([],[]) globalThmEdges
    nextDGraph = fst result
    nextHistoryElem = snd result

{- alle kanten vom Typ GlobalThm holen, 
zur "Verarbeitung" an Hilfsfunktion weitergeben
 -}


globSubsumeAux :: DGraph -> ([DGRule],[DGChange]) -> [LEdge DGLinkLab]
	            -> (DGraph,([DGRule],[DGChange]))
globSubsumeAux dGraph historyElement [] = (dGraph, historyElement)
globSubsumeAux dGraph (rules,changes) ((ledge@(source,target,edgeLab)):list) =    if existsDefPathOfSameMorphism dGraph morphism source target
     then -- kante aus Graph löschen, stattdessen def einfügen
       globSubsumeAux newGraph (rules,changes) list
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

{- schauen, ob ein Pfad von GlobalDefs von source nach target geht
falls ja: kante löschen, stattdessen GlobalDef von source nach target einfügen
falls nein: nichts tun
mit den übrigen kanten weitermachen -}
{-
existsDefPath :: DGraph -> GMorphism -> Node -> Node -> Bool
existsDefPath dGraph morphism src tgt =
  existsDefPathAux dGraph morphism [] (src:[]) tgt


existsDefPathAux :: DGraph  -> GMorphism -> [LEdge DGLinkLab] 
		 -> [Node] -> Node -> Bool
existsDefPathAux _ _ _ [] _ = False
existsDefPathAux dGraph morphism path nodes target =

  if (elem target nodes) and (morphism == (calculateMorphism path edge))then True
   else existsDefPathAux dGraph sucNodes target
  where
    outGoingEdges = concatMap (out dGraph) sourceNodes
    globalDefEdges = filter isGlobalDef outGoingEdges
    sucNodes = map getTargetNode globalDefEdges



BBBB AAAA U  U SSSS TTTTT EEEE L    L    EEEE
B  B A  A U  U S      T   E    L    L    E   
BBBB AAAA U  U SSSS   T   EEEE L    L    EEEE
B  B A  A U  U    S   T   E    L    L    E   
BBBB A  A UUUU SSSS   T   EEEE LLLL LLLL EEEE

-}

-- existsDefPathOfSameMorphism :: DGraph -> GMorphism -> Node -> Node -> True
existsDefPathOfSameMorphism dgraph morphism src tgt =
  undefined

  where 
    outGoingEdges = out dgraph src
    globalDefEdges = filter isGlobalDef outGoingEdges
    defEdgesToTgt = [edge| edge <- globalDefEdges, tgt == getTargetNode edge]






--getMorphismOfPath :: [LEdge DGLinkLab] -> GMorphism -> GMorphism
getMorphismOfPath [] morphism = morphism
getMorphismOfPath path@((src,tgt,edgeLab):furtherPath) morphism =
  getMorphismOfPath furtherPath newMorphism

  where newMorphism = calculateMorphism (dgl_type edgeLab) morphism

--calculateMorphism :: GMorphism -> GMorphism -> GMorphism
calculateMorphism morph1 morph2 = error "calculateMorphism not yet implemented"


getTargetNode :: LEdge DGLinkLab -> Node
getTargetNode (_,target,_) = target

isUnprovenGlobalThm :: LEdge DGLinkLab -> Bool
isUnprovenGlobalThm (_,_,edgeLab) = case dgl_type edgeLab of
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
