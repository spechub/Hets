{- | 
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

theorem hide shift proof in development graphs.
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

module Proofs.TheoremHideShift (theoremHideShift) where

import Data.List(partition)

import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Common.Utils
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map
import Syntax.AS_Library
import Proofs.EdgeUtils
import Proofs.StatusUtils

{- | returns the sentence list of the given node -}
getSignature :: LibEnv -> DGraph -> Node -> Maybe G_sign
getSignature libEnv dgraph node =
  if isDGRef nodeLab
    then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just (_,_,refDgraph) -> 
         getSignature libEnv refDgraph (dgn_node nodeLab)
      Nothing -> Nothing
    else Just (dgn_sign nodeLab)
    where nodeLab = lab' $ safeContext 
                    "Proofs.TheoremHideShift.getSignature" dgraph node

-- ----------------------------------------------
-- theorem hide shift
-- ----------------------------------------------

theoremHideShift :: ProofStatus -> ProofStatus
theoremHideShift proofStatus@(ln,_,_) =
  let (nonLeaves,leaves) 
          = partition (hasIngoingHidingDef proofStatus ln) $ 
            nodes $ lookupDGraph ln proofStatus
      auxProofstatus = handleLeaves (prepareProofStatus proofStatus) leaves
      finalProofstatus = handleNonLeaves auxProofstatus nonLeaves
  in reviseProofStatus finalProofstatus

-- bei DGRefs auch ueber lib-Grenze hinaus suchen?
{- | returns True, if the given node has at least one directely or
   indirectely (ie via an ingoing path of GlobalDef edges) 
   ingoing HidingDef edge. returns False otherwise
 -}
hasIngoingHidingDef :: ProofStatus -> LIB_NAME -> Node -> Bool
hasIngoingHidingDef proofstatus@(_,libEnv,_) ln node =
  not (null hidingDefEdges) 
   || or [hasIngoingHidingDef proofstatus ln' nod| (ln',nod) <- next]
  where
    inGoingEdges = getAllIngoingEdges libEnv (ln,node)
    hidingDefEdges = [tuple| tuple <- inGoingEdges, isHidingDef (snd tuple)]
    globalDefEdges = [tuple| tuple <- inGoingEdges, isGlobalDef (snd tuple)]
    next = [ (l,getSourceNode e) | (l,e) <- globalDefEdges ]

{- | handles all nodes that are leaves
   (ie nodes that have no ingoing edges of type HidingDef) -}
handleLeaves :: ProofStatus -> [Node] -> ProofStatus
handleLeaves = foldl convertToNf

{- | converts the given node to its own normal form -}
convertToNf :: ProofStatus -> Node -> ProofStatus
convertToNf proofstatus@(ln, _, _) node =
  let dgraph = lookupDGraph ln proofstatus
      nodelab = lab' $ safeContext 
                "Proofs.TheoremHideShift.convertToNf" dgraph node
  in case dgn_nf nodelab of
    Just _ -> proofstatus
    Nothing ->
      let newNode = getNewNode dgraph
          proofstatusAux = mkNfNodeForLeave node newNode proofstatus
          auxGraph = lookupDGraph ln proofstatusAux
          (finalGraph, changes) = adoptEdges auxGraph node newNode
          finalChanges =  changes ++ [DeleteNode (node,nodelab)]
      in updateProofStatus ln (delNode node finalGraph)
              finalChanges proofstatusAux

{- | creates and inserts a normal form node from the given input -}
mkNfNodeForLeave :: Node -> Node  -> ProofStatus -> ProofStatus
mkNfNodeForLeave node newNode proofstatus@(ln,_,_) =
  let nodelab = lab' $ safeContext "Proofs.TheoremHideShift.mkNfNodeForLeave" 
                      (lookupDGraph ln proofstatus) node
  in case isDGRef nodelab of
    True -> mkDGRefNfNode nodelab newNode True proofstatus
    False -> mkDGNodeNfNode nodelab newNode Nothing proofstatus

{- | creates and inserts a normal form node of type DGNode:
   if the given nonLeaveValues is Nothing, ie the original node is a leave,
   the original node is copied and the dgn_sigma is the identity;
   if not, dgn_sign and dgn_sigma are taken from the nonLeaveValues and
   the remaining values are copied from the original node;
   in both cases the normal form node ist its own normal form -}
mkDGNodeNfNode :: DGNodeLab -> Node -> Maybe (G_theory, Maybe GMorphism)
               -> ProofStatus -> ProofStatus
mkDGNodeNfNode nodelab newNode nonLeaveValues proofstatus = 
  let (th,sigma) = case nonLeaveValues of
                       Nothing -> (dgn_theory nodelab,
                                  Just (ide Grothendieck (dgn_sign nodelab)))
                       Just x -> x
      lnode = (newNode,
         DGNode {dgn_name = dgn_name nodelab,
                 dgn_theory = th,
                 dgn_nf = Just newNode,
                 dgn_sigma = sigma,
                 dgn_origin = DGProof,
                 dgn_cons = None,
                 dgn_cons_status = LeftOpen
                })
  in insertNfNode proofstatus lnode

{- | creates and inserts a normal form node of type DGRef:
   if the given corresponding node is a leave, the normal form node
   of the referenced node is referenced and its values copied;
   if not, the original node is copied and the dgn_sigma is the identiy;
   in both cases the normal form node is its own normal form -}
mkDGRefNfNode :: DGNodeLab -> Node -> Bool -> ProofStatus -> ProofStatus
mkDGRefNfNode nodelab newNode isLeave proofstatus@(ln,_,_) =
  let auxProofstatus@(_,auxLibEnv,_) = theoremHideShift 
                    (changeCurrentLibName (dgn_libname nodelab) proofstatus)
      refGraph = lookupDGraph (dgn_libname nodelab) proofstatus
      (Just refNf) = dgn_nf $ lab' $ safeContext 
               "Proofs.TheoremHideShift.mkDGRefNfNode" 
               refGraph $ dgn_node nodelab
      refNodelab = lab' (safeContext 
                         "Proofs.TheoremHideShift.mkDGRefNfNode" 
                         refGraph refNf)
      (renamed, libname, sigma) =
          if isLeave 
             then (dgn_name nodelab, dgn_libname nodelab,
                   case getSignature auxLibEnv refGraph refNf of
                     Nothing -> Nothing
                     Just sign -> Just (ide Grothendieck sign)
                  )
           else (dgn_name refNodelab, dgn_libname refNodelab,
                          dgn_sigma refNodelab)
      lnode = (newNode,
               DGRef {dgn_name = renamed,
                      dgn_libname = libname,
                      dgn_node = refNf,
                      dgn_theory = error "mkDGRefNfNode",
                      dgn_nf = Just newNode,
                      dgn_sigma = sigma
                     })
  in insertNfNode (changeCurrentLibName ln auxProofstatus) lnode

{- | inserts the given node into the development graph belonging
   to the given library name and updates the proofstatus -}
insertNfNode :: ProofStatus -> LNode DGNodeLab -> ProofStatus
insertNfNode proofstatus@(ln,_,_) dgnode =
  updateProofStatus ln 
                    (insNode dgnode (lookupDGraph ln proofstatus))
                    [InsertNode dgnode]
                    proofstatus

{- | handles all nodes that are no leaves
   (ie nodes that have ingoing edges of type HidingDef) -}
handleNonLeaves :: ProofStatus -> [Node] -> ProofStatus
handleNonLeaves proofstatus [] = proofstatus
handleNonLeaves proofstatus@(ln,_,_) (node:list) =
  let dgraph = lookupDGraph ln proofstatus
      nodelab = lab' (safeContext "Proofs.TheoremHideShift.handleNonLeaves" 
                                  dgraph node)
  in case dgn_nf nodelab of
    Just _ -> handleNonLeaves proofstatus list
    Nothing ->
      case isDGRef nodelab of
        True -> 
          let nfNode = getNewNode dgraph
              auxProofstatus' = mkDGRefNfNode nodelab nfNode False proofstatus
              (auxGraph, changes) = setNfOfNode dgraph node nfNode
              finalProofstatus = updateProofStatus ln auxGraph changes
                                 auxProofstatus'
          in handleNonLeaves finalProofstatus list
        False -> 
          let auxProofstatus = createNfsForPredecessors proofstatus node
              auxGraph = lookupDGraph ln auxProofstatus
              defInEdges = [edge| edge <- inn auxGraph node,
                           isGlobalDef edge || isHidingDef edge]
              predecessors = [src| (src,_,_) <- defInEdges]
              diagram = makeDiagram auxGraph (node:predecessors) defInEdges
              Result _ds res = gWeaklyAmalgamableCocone diagram
          in case res of
            Nothing -> -- do sequence $ map (putStrLn . show) diags
                          handleNonLeaves auxProofstatus list
            Just (sign, mmap) -> 
              let nfNode = getNewNode auxGraph
                  sigma = Map.lookup node mmap
                  auxProofstatus' = mkDGNodeNfNode nodelab nfNode 
                                    (Just (sign,sigma)) auxProofstatus
-- use this line until gWeaklyAmalgamableCocone is defined: 
--        (Just (dgn_sign nodelab,sigma))            
                  finalProofstatus = linkNfNode node nfNode mmap 
                                     auxProofstatus'
              in handleNonLeaves finalProofstatus list
                          
{- | creates the normal forms of the predecessors of the given node
   note: as this method it is called after the normal forms of the leave nodes
   have already been defined, only handleNonLeaves is called here -}
createNfsForPredecessors :: ProofStatus -> Node -> ProofStatus
createNfsForPredecessors proofstatus@(ln,_,_) node =
  handleNonLeaves proofstatus predecessors
  where
    dgraph = lookupDGraph ln proofstatus
    defInEdges =  [edge| edge@(src,_,_) <- inn dgraph node,
                   (isGlobalDef edge || isHidingDef edge) 
                   && node /= src]
    predecessors = [src| (src,_,_) <- defInEdges]

{- | creates an GDiagram with the signatures of the given nodes as nodes
   and the morphisms of the given edges as edges -}
makeDiagram :: DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagram = makeDiagramAux empty


{- | auxiliary method for makeDiagram: first translates all nodes then
   all edges, the descriptors of the nodes are kept in order to make
   retranslation easier -}
makeDiagramAux :: GDiagram -> DGraph -> [Node] -> [LEdge DGLinkLab] -> GDiagram
makeDiagramAux diagram _ [] [] = diagram
makeDiagramAux diagram dgraph [] (edge@(src,tgt,labl):list) =
  makeDiagramAux (insEdge morphEdge diagram) dgraph [] list
    where morphEdge = if isHidingDef edge then (tgt,src,dgl_morphism labl) 
                       else (src,tgt,dgl_morphism labl)
makeDiagramAux diagram dgraph (node:list) es =
  makeDiagramAux (insNode sigNode diagram) dgraph list es
    where sigNode = (node, dgn_theory $ lab' $ safeContext 
                "Proofs.TheoremHideShift.makeDiagramAux" dgraph node)

{- | sets the normal form of the first given node to the second one and
   insert the edges to the normal form node according to the given map -}
linkNfNode :: Node -> Node -> Map.Map Node GMorphism -> ProofStatus
           -> ProofStatus
linkNfNode node nfNode mmap proofstatus@(ln,_,_) =
  let (auxGraph, changes) = 
          setNfOfNode (lookupDGraph ln proofstatus) node nfNode
      (finalGraph,changes') = insertEdgesToNf auxGraph nfNode mmap
  in updateProofStatus ln finalGraph (changes ++ changes') proofstatus

{- | sets the normal form of the first node to the second one -}
setNfOfNode :: DGraph -> Node -> Node -> (DGraph,[DGChange])
setNfOfNode dgraph node nf_node = 
  let (finalGraph,changes) = adoptEdges auxGraph node newNode
  in (delNode node finalGraph,
          InsertNode newLNode : changes ++ [DeleteNode oldLNode])
  where
    nodeCtx = safeContext "Proofs.TheoremHideShift.setNfOfNode" dgraph node
    nodeLab = lab' nodeCtx
    oldLNode = labNode' nodeCtx
    newNode = getNewNode dgraph
    newLNode = case isDGRef nodeLab of
                 True -> (newNode, DGRef {dgn_name = dgn_name nodeLab,
                                          dgn_libname = dgn_libname nodeLab,
                                          dgn_node = dgn_node nodeLab,
                                          dgn_theory = error "setNfOfNode",
                                                 -- dgn_theory nodeLab, -- ?
                                          dgn_nf = Just nf_node,
                                          dgn_sigma = dgn_sigma nodeLab
                                         })
                 False -> (newNode, DGNode {dgn_name = dgn_name nodeLab,
                                            dgn_theory = dgn_theory nodeLab,
                                            dgn_nf = Just nf_node,
                                            dgn_sigma = dgn_sigma nodeLab,
                                            dgn_origin = DGProof,
                                            dgn_cons = None,
                                            dgn_cons_status = LeftOpen
                                           })
    auxGraph = insNode newLNode dgraph

{- | inserts GlobalDef edges to the given node from each node in the map
   with the corresponding morphism -}
insertEdgesToNf :: DGraph -> Node -> Map.Map Node GMorphism
                   -> (DGraph,[DGChange])
insertEdgesToNf dgraph nfNode mmap =
    insertEdgesToNfAux dgraph nfNode $ Map.toList mmap
    
{- | auxiliary method for insertEdgesToNf -}
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
