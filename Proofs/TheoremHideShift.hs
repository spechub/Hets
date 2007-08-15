{- |
Module      :  $Header$
Description :  theorem hide shift proof rule for development graphs
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

theorem hide shift proof rule for development graphs
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

module Proofs.TheoremHideShift (theoremHideShift,
                                theoremHideShiftFromList) where

import Data.List(partition)

import Logic.Logic
import Logic.Grothendieck
import Static.GTheory
import Static.DevGraph
import Static.DGToSpec
import Common.Result
import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import Syntax.AS_Library
import Proofs.EdgeUtils
import Proofs.StatusUtils

{- | returns the sentence list of the given node -}
getSignature :: LibEnv -> DGraph -> Node -> Maybe G_sign
getSignature libEnv dgraph node =
  if isDGRef nodeLab
    then case Map.lookup (dgn_libname nodeLab) libEnv of
      Just dg ->
         getSignature libEnv dg (dgn_node nodeLab)
      Nothing -> Nothing
    else Just (dgn_sign nodeLab)
    where nodeLab = lab' $ safeContextDG
                    "Proofs.TheoremHideShift.getSignature" dgraph node

-- ----------------------------------------------
-- theorem hide shift
-- ----------------------------------------------

theoremHideShift :: LIB_NAME -> LibEnv -> LibEnv
theoremHideShift ln proofStatus =
  let (nonLeaves,leaves)
          = partition (hasIngoingHidingDef proofStatus ln) $
            nodesDG $ lookupDGraph ln proofStatus
      auxProofstatus = handleLeaves ln (prepareProofStatus proofStatus) leaves
      finalProofstatus = handleNonLeaves ln auxProofstatus nonLeaves
  in reviseProofStatus finalProofstatus


theoremHideShiftFromList :: LIB_NAME -> [LNode DGNodeLab] 
                              -> LibEnv -> LibEnv
theoremHideShiftFromList ln ls proofStatus =
  let nbls x = case x of
                []        -> []
                (nb,_):ll -> nb:(nbls ll)
      (nonLeaves, leaves)
          = partition (hasIngoingHidingDef proofStatus ln) (nbls ls)
      auxProofstatus = handleLeaves ln (prepareProofStatus proofStatus) leaves
      finalProofstatus = handleNonLeaves ln auxProofstatus nonLeaves
  in reviseProofStatus finalProofstatus

-- bei DGRefs auch ueber lib-Grenze hinaus suchen?
{- | returns True, if the given node has at least one directely or
   indirectely (ie via an ingoing path of GlobalDef edges)
   ingoing HidingDef edge. returns False otherwise
 -}
hasIngoingHidingDef :: LibEnv -> LIB_NAME -> Node -> Bool
hasIngoingHidingDef libEnv ln node =
  not (null hidingDefEdges)
   || or [hasIngoingHidingDef libEnv ln' nod | (ln',nod) <- next]
  where
    inGoingEdges = getAllIngoingEdges libEnv ln node
    hidingDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isHidingDef n]
    globalDefEdges = [tuple| tuple@(_, n) <- inGoingEdges, liftE isGlobalDef n]
    next = [ (l, s) | (l, (s, _, _)) <- globalDefEdges ]

getAllIngoingEdges :: LibEnv -> LIB_NAME -> Node
                   -> [(LIB_NAME, LEdge DGLinkLab)]
getAllIngoingEdges libEnv ln node =
  case isDGRef nodelab of
    False -> inEdgesInThisGraph
    True -> inEdgesInThisGraph ++ inEdgesInRefGraph
  where
    dgraph = lookupDGraph ln libEnv
    nodelab = lab' $ safeContextDG "Static.DGToSpec.getAllIngoingEdges"
              dgraph node
    inEdgesInThisGraph = [(ln,inEdge)| inEdge <- innDG dgraph node]
    refLn = dgn_libname nodelab
    refGraph = lookupDGraph refLn libEnv
    refNode = dgn_node nodelab
    inEdgesInRefGraph = [(refLn,inEdge)| inEdge <- innDG refGraph refNode]

{- | handles all nodes that are leaves
   (ie nodes that have no ingoing edges of type HidingDef) -}
handleLeaves :: LIB_NAME -> LibEnv -> [Node] -> LibEnv
handleLeaves ln = foldl (convertToNf ln)

{- | converts the given node to its own normal form -}
convertToNf :: LIB_NAME -> LibEnv -> Node -> LibEnv
convertToNf ln proofstatus node =
  let dgraph = lookupDGraph ln proofstatus
      nodelab = lab' $ safeContextDG
                "Proofs.TheoremHideShift.convertToNf" dgraph node
  in case dgn_nf nodelab of
    Just _ -> proofstatus
    Nothing ->
      let newNode = getNewNodeDG dgraph
          proofstatusAux = mkNfNodeForLeave ln node newNode proofstatus
          auxGraph = lookupDGraph ln proofstatusAux
          (finalGraph, changes) = adoptEdges auxGraph node newNode
          finalChanges =  changes ++ [DeleteNode (node,nodelab)]
      in updateProofStatus ln (delNodeDG node finalGraph)
              finalChanges proofstatusAux

{- | creates and inserts a normal form node from the given input -}
mkNfNodeForLeave :: LIB_NAME -> Node -> Node  -> LibEnv -> LibEnv
mkNfNodeForLeave ln node newNode proofstatus =
  let nodelab = lab' $ safeContextDG "Proofs.TheoremHideShift.mkNfNodeForLeave"
                      (lookupDGraph ln proofstatus) node
  in case isDGRef nodelab of
    True -> mkDGRefNfNode ln nodelab newNode True proofstatus
    False -> mkDGNodeNfNode ln nodelab newNode Nothing proofstatus

{- | creates and inserts a normal form node of type DGNode:
   if the given nonLeaveValues is Nothing, ie the original node is a leave,
   the original node is copied and the dgn_sigma is the identity;
   if not, dgn_sign and dgn_sigma are taken from the nonLeaveValues and
   the remaining values are copied from the original node;
   in both cases the normal form node ist its own normal form -}
mkDGNodeNfNode :: LIB_NAME -> DGNodeLab -> Node
               -> Maybe (G_theory, Maybe GMorphism)
               -> LibEnv -> LibEnv
mkDGNodeNfNode ln nodelab newNode nonLeaveValues proofstatus =
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
  in insertNfNode ln proofstatus lnode

{- | creates and inserts a normal form node of type DGRef:
   if the given corresponding node is a leave, the normal form node
   of the referenced node is referenced and its values copied;
   if not, the original node is copied and the dgn_sigma is the identiy;
   in both cases the normal form node is its own normal form -}
mkDGRefNfNode :: LIB_NAME -> DGNodeLab -> Node -> Bool
              -> LibEnv -> LibEnv
mkDGRefNfNode ln nodelab newNode isLeave proofstatus =
  let auxProofstatus@auxLibEnv = theoremHideShift
                    (dgn_libname nodelab) proofstatus
      refGraph = lookupDGraph (dgn_libname nodelab) proofstatus
      (Just refNf) = dgn_nf $ lab' $ safeContextDG
               "Proofs.TheoremHideShift.mkDGRefNfNode"
               refGraph $ dgn_node nodelab
      refNodelab = lab' (safeContextDG
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
  in insertNfNode ln auxProofstatus lnode

{- | inserts the given node into the development graph belonging
   to the given library name and updates the proofstatus -}
insertNfNode :: LIB_NAME -> LibEnv -> LNode DGNodeLab -> LibEnv
insertNfNode ln proofstatus dgnode =
  updateProofStatus ln newDGraph newChange proofstatus
  where
  (newDGraph, newChange) = updateWithOneChange (InsertNode dgnode) 
					       (lookupDGraph ln proofstatus) 
					       []
{-
  updateProofStatus ln
                    (insNode dgnode (lookupDGraph ln proofstatus))
                    [InsertNode dgnode]
                    proofstatus
-}

{- | handles all nodes that are no leaves
   (ie nodes that have ingoing edges of type HidingDef) -}
handleNonLeaves :: LIB_NAME -> LibEnv -> [Node] -> LibEnv
handleNonLeaves _ ps [] = ps
handleNonLeaves ln ps (node:list) =
  let dgraph = lookupDGraph ln ps
      nodelab = lab' (safeContextDG "Proofs.TheoremHideShift.handleNonLeaves"
                                  dgraph node)
  in case dgn_nf nodelab of
    Just _ -> handleNonLeaves ln ps list
    Nothing ->
      case isDGRef nodelab of
        True ->
          let nfNode = getNewNodeDG dgraph
              auxProofstatus' = mkDGRefNfNode ln nodelab nfNode False ps
              (auxGraph, changes) = setNfOfNode dgraph node nfNode
              finalProofstatus = updateProofStatus ln auxGraph changes
                                 auxProofstatus'
          in handleNonLeaves ln finalProofstatus list
        False ->
          let auxProofstatus = createNfsForPredecessors ln ps node
              auxGraph = lookupDGraph ln auxProofstatus
              defInEdges = [edge| edge <- innDG auxGraph node,
                           liftE (liftOr isGlobalDef isHidingDef) edge]
              predecessors = [src| (src,_,_) <- defInEdges]
              diagram = makeDiagram auxGraph (node:predecessors) defInEdges
              Result _ds res = gWeaklyAmalgamableCocone diagram
          in case res of
            Nothing -> -- do sequence $ map (putStrLn . show) diags
                          handleNonLeaves ln auxProofstatus list
            Just (sign, mmap) ->
              let nfNode = getNewNodeDG auxGraph
                  sigma = Map.lookup node mmap
                  auxProofstatus' = mkDGNodeNfNode ln nodelab nfNode
                                    (Just (sign,sigma)) auxProofstatus
-- use this line until gWeaklyAmalgamableCocone is defined:
--        (Just (dgn_sign nodelab,sigma))
                  finalProofstatus = linkNfNode ln node nfNode mmap
                                     auxProofstatus'
              in handleNonLeaves ln finalProofstatus list

{- | creates the normal forms of the predecessors of the given node
   note: as this method it is called after the normal forms of the leave nodes
   have already been defined, only handleNonLeaves is called here -}
createNfsForPredecessors :: LIB_NAME -> LibEnv -> Node -> LibEnv
createNfsForPredecessors ln proofstatus node =
  handleNonLeaves ln proofstatus predecessors
  where
    dgraph = lookupDGraph ln proofstatus
    defInEdges =  [edge| edge@(src,_,_) <- innDG dgraph node,
                   liftE (liftOr isGlobalDef isHidingDef) edge
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
    where morphEdge = if liftE isHidingDef edge 
                      then (tgt,src,dgl_morphism labl)
                      else (src,tgt,dgl_morphism labl)
makeDiagramAux diagram dgraph (node:list) es =
  makeDiagramAux (insNode sigNode diagram) dgraph list es
    where sigNode = (node, dgn_theory $ lab' $ safeContextDG
                "Proofs.TheoremHideShift.makeDiagramAux" dgraph node)

{- | sets the normal form of the first given node to the second one and
   insert the edges to the normal form node according to the given map -}
linkNfNode :: LIB_NAME -> Node -> Node -> Map.Map Node GMorphism -> LibEnv
           -> LibEnv
linkNfNode ln node nfNode mmap proofstatus =
  let (auxGraph, changes) =
          setNfOfNode (lookupDGraph ln proofstatus) node nfNode
      (finalGraph,changes') = insertEdgesToNf auxGraph nfNode mmap
  in updateProofStatus ln finalGraph (changes ++ changes') proofstatus

{- | sets the normal form of the first node to the second one -}
setNfOfNode :: DGraph -> Node -> Node -> (DGraph,[DGChange])
setNfOfNode dgraph node nf_node =
  let (finalGraph,changes) = adoptEdges auxGraph node newNode
  in (delNodeDG node finalGraph,
          InsertNode newLNode : changes ++ [DeleteNode oldLNode])
  where
    nodeCtx = safeContextDG "Proofs.TheoremHideShift.setNfOfNode" dgraph node
    nodeLab = lab' nodeCtx
    oldLNode = labNode' nodeCtx
    newNode = getNewNodeDG dgraph
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
    auxGraph = insNodeDG newLNode dgraph

{- | inserts GlobalDef edges to the given node from each node in the map
   with the corresponding morphism -}
insertEdgesToNf :: DGraph -> Node -> Map.Map Node GMorphism
                   -> (DGraph,[DGChange])
insertEdgesToNf dgraph nfNode mmap =
    insertEdgesToNfAux dgraph nfNode $ Map.toList mmap

{- | auxiliary method for insertEdgesToNf -}
insertEdgesToNfAux :: DGraph -> Node -> [(Node,GMorphism)]
                   -> (DGraph,[DGChange])
insertEdgesToNfAux dgraph nfNode list =
       updateWithChanges [InsertEdge $ makeEdge node nfNode morph|(node, morph)<-list] dgraph []
       where
       makeEdge src tgt m = (src, tgt, DGLink {
					      dgl_morphism = m,
					      dgl_type = GlobalDef,
					      dgl_origin = DGProof,
					      dgl_id = defaultEdgeID
					      })

{-
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
-}
