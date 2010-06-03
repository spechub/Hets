{- |
Module      :  $Header$
Description :  Data types and functions for architectural diagrams
Copyright   :  (c) Maciek Makowski, Warsaw University 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (Logic)

   Data types and functions for architectural diagrams
   Follows the CASL Reference Manual, section III.5.6.

   Extended to the new rules for lambda expressions(WADT2010).

-}

module Static.ArchDiagram where

import Logic.Comorphism
import Logic.Logic
import Logic.Grothendieck
import Logic.Coerce

import Data.Graph.Inductive.Graph as Graph
import qualified Common.Lib.Graph as Tree

import qualified Data.Map as Map
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Result
import Common.Id

import Static.GTheory
import Static.DevGraph

-- * Types
-- (as defined for extended static semantics in Chap. III:5.6.1)

-- moved in Static.DevGraph

emptyDiag :: Diag
emptyDiag = Diagram{diagGraph = Graph.empty, numberOfEdges = 0}

data DiagNodeSig = Diag_node_sig Node NodeSig deriving Show

instance Show MaybeDiagNode where
 show (EmptyDiagNode _) = "empty"
 show (JustDiagNode dns) = show dns

data MaybeDiagNode = JustDiagNode DiagNodeSig | EmptyDiagNode AnyLogic

toMaybeNode :: MaybeDiagNode -> MaybeNode
toMaybeNode mdn = case mdn of
    JustDiagNode dns -> JustNode $ getSigFromDiag dns
    EmptyDiagNode l -> EmptyNode l

-- | Return a signature stored within given diagram node sig
getSigFromDiag :: DiagNodeSig -> NodeSig
getSigFromDiag (Diag_node_sig _ ns) = ns

data BasedUnitSig = Based_unit_sig DiagNodeSig RefSig
                  | Based_par_unit_sig MaybeDiagNode RefSig
                  | Based_lambda_unit_sig [DiagNodeSig] RefSig
                    -- the list is always non-empty,
                    -- actually has at least 2 elems, and the
                    -- head stores the "result" node

instance Show BasedUnitSig where
 show (Based_unit_sig dns _) = show dns
 show (Based_par_unit_sig mdn _) = show mdn
 show (Based_lambda_unit_sig _ usig) = show usig

type StBasedUnitCtx = Map.Map SIMPLE_ID BasedUnitSig
emptyStBasedUnitCtx :: StBasedUnitCtx
emptyStBasedUnitCtx = Map.empty

-- Since Ps and Bs in the definition of ExtStUnitCtx have disjoint domains
-- we can merge them into a single mapping represented by StBasedUnitCtx.
type ExtStUnitCtx = (StBasedUnitCtx, Diag)
emptyExtStUnitCtx :: ExtStUnitCtx
emptyExtStUnitCtx = (emptyStBasedUnitCtx, emptyDiag)

-- Instance
instance Pretty Diag where
    pretty diag =
        let gs (n, dn) =
                (n, getSig $ dn_sig dn)
        in text "nodes:"
           <+> sepByCommas (map (pretty . gs) $ labNodes $ diagGraph diag)
           $+$ text "edges:"
           <+> ppWithCommas (edges $ diagGraph diag)

-- * Functions

-- | return the diagram
printDiag :: a -> String -> Diag -> Result a
printDiag res _ _ = return res

-- | A mapping from extended to basic static unit context
ctx :: ExtStUnitCtx -> RefStUnitCtx
ctx (buc, _) =
    let ctx' [] _ = emptyRefStUnitCtx
        ctx' (id1 : ids) buc0 =
            let uctx = ctx' ids buc0
            in case Map.lookup id1 buc0 of
                    Just (Based_unit_sig _ rsig) -> Map.insert id1
                           rsig uctx
                    Just (Based_par_unit_sig _ rsig) -> Map.insert id1
                           rsig uctx
                    Just (Based_lambda_unit_sig _ rsig) -> Map.insert id1
                          rsig uctx
                    _ -> uctx -- this should never be the case
    in ctx' (Map.keys buc) buc

-- | Insert the edges from given source nodes to given target node
-- into the given diagram. The edges are labelled with inclusions.
insInclusionEdges :: LogicGraph
                  -> Diag -- ^ the diagram to insert edges to
                  -> [DiagNodeSig] -- ^ the source nodes
                  -> DiagNodeSig   -- ^ the target node
                  -> Result Diag -- ^ the diagram with edges inserted
insInclusionEdges lgraph diag0 srcNodes (Diag_node_sig tn tnsig) = do
 let inslink diag dns = do
     d1 <- diag
     let d = diagGraph d1
     case dns of
       Diag_node_sig n nsig -> do
        incl <- ginclusion lgraph (getSig nsig) (getSig tnsig)
        return $ Diagram {diagGraph = insEdge (n, tn, DiagLink {
                                 dl_morphism = incl,
                                 dl_number = numberOfEdges d1 + 1 }) d,
                          numberOfEdges = numberOfEdges d1 + 1}
 diag' <- foldl inslink (return diag0) srcNodes
 return diag'

-- | Insert the edges from given source node to given target nodes
-- into the given diagram. The edges are labelled with inclusions.
insInclusionEdgesRev :: LogicGraph
                     -> Diag -- ^ the diagram to insert edges to
                     -> DiagNodeSig   -- ^ the source node
                     -> [DiagNodeSig] -- ^ the target nodes
                     -> Result Diag -- ^ the diagram with edges inserted
insInclusionEdgesRev lgraph diag0 (Diag_node_sig sn snsig) targetNodes =
    do let inslink diag dns = do
               d1 <- diag
               let d = diagGraph d1
               case dns of
                 Diag_node_sig n nsig -> do
                   incl <- ginclusion lgraph (getSig snsig) (getSig nsig)
                   return $ Diagram {diagGraph = insEdge (sn, n, DiagLink {
                      dl_morphism = incl,
                      dl_number = numberOfEdges d1 + 1 }) d,
                                     numberOfEdges = numberOfEdges d1 + 1}
       diag' <- foldl inslink (return diag0) targetNodes
       return diag'

{- | Build a diagram that extends given diagram with a node containing
given signature and with edges from given set of nodes to the new
node.  The new edges are labelled with sigature inclusions. -}
extendDiagramIncl :: LogicGraph
                  -> Diag          -- ^ the diagram to be extended
                  -> [DiagNodeSig]
                  -- ^ the nodes which should be linked to the new node
                  -> NodeSig
                  -- ^ the signature with which the new node should be labelled
                  -> String        -- ^ the node description (for diagnostics)
                  -> Result (DiagNodeSig, Diag)
-- ^ returns the new node and the extended diagram
extendDiagramIncl lgraph diag srcNodes newNodeSig desc =
  do let nodeContents = DiagNode {dn_sig = newNodeSig, dn_desc = desc}
         diagGr = diagGraph diag
         node = Tree.getNewNode diagGr
         diag' = Diagram{diagGraph = insNode (node, nodeContents) diagGr,
                         numberOfEdges = numberOfEdges diag}
         newDiagNode = Diag_node_sig node newNodeSig
     diag'' <- insInclusionEdges lgraph diag' srcNodes newDiagNode
     printDiag (newDiagNode, diag'') "extendDiagramIncl" diag''

-- | Extend the development graph with given morphism originating
-- from given NodeSig
extendDGraph :: DGraph    -- ^ the development graph to be extended
             -> NodeSig   -- ^ the NodeSig from which the morphism originates
             -> GMorphism -- ^ the morphism to be inserted
             -> DGOrigin
             -> Result (NodeSig, DGraph)
-- ^ returns the target signature of the morphism and the resulting DGraph
extendDGraph dg (NodeSig n _) morph orig = case cod morph of
    targetSig@(G_sign lid tar ind) -> let
      nodeContents = newNodeLab emptyNodeName orig
        $ noSensGTheory lid tar ind
      linkContents = globDefLink morph SeeTarget
      node = getNewNodeDG dg
      dg' = insNodeDG (node, nodeContents) dg
      dg'' = snd $ insLEdgeDG (n, node, linkContents) dg'
      in return (NodeSig node targetSig, dg'')

-- | Extend the development graph with given morphism pointing to
-- given NodeSig
extendDGraphRev :: DGraph    -- ^ the development graph to be extended
             -> NodeSig   -- ^ the NodeSig to which the morphism points
             -> GMorphism -- ^ the morphism to be inserted
             -> DGOrigin
             -> Result (NodeSig, DGraph)
-- ^ returns the source signature of the morphism and the resulting DGraph
extendDGraphRev dg (NodeSig n _) morph orig = case dom morph of
    sourceSig@(G_sign lid src ind) -> let
      nodeContents = newNodeLab emptyNodeName orig
        $ noSensGTheory lid src ind
      linkContents = globDefLink morph SeeSource
      node = getNewNodeDG dg
      dg' = insNodeDG (node, nodeContents) dg
      dg'' = snd $ insLEdgeDG (node, n, linkContents) dg'
      in return (NodeSig node sourceSig, dg'')

{- | Build a diagram that extends the given diagram with a node and an
edge to that node. The edge is labelled with a given signature morphism
and the node contains the target of this morphism. Extends the
development graph with the given morphism as well. -}
extendDiagramWithMorphism :: Range         -- ^ the position (for diagnostics)
                          -> LogicGraph
                          -> Diag          -- ^ the diagram to be extended
                          -> DGraph        -- ^ the development graph
                          -> DiagNodeSig
                          -- ^ the node from which the edge should originate
                          -> GMorphism
                          -- ^ the morphism as label for the new edge
                          -> String -- ^ the node description (for diagnostics)
                          -> DGOrigin -- ^ the origin of the new node
                          -> Result (DiagNodeSig, Diag, DGraph)
-- ^ returns the new node, the extended diagram and extended development graph
extendDiagramWithMorphism pos _ diag dg (Diag_node_sig n nsig) mor desc orig =
  if getSig nsig == dom mor then
     do (targetSig, dg') <- extendDGraph dg nsig mor orig
        let nodeContents = DiagNode {dn_sig = targetSig, dn_desc = desc}
            diagGr = diagGraph diag
            node = Tree.getNewNode diagGr
            diagGr' = insNode (node, nodeContents) diagGr
            diag' = Diagram{diagGraph = insEdge (n, node, DiagLink {
                               dl_morphism = mor,
                               dl_number = numberOfEdges diag + 1 }) diagGr',
                            numberOfEdges = numberOfEdges diag + 1 }
        printDiag (Diag_node_sig node targetSig, diag', dg')
                      "extendDiagramWithMorphism" diag'
     else fatal_error
     ("Internal error: Static.ArchDiagram.extendDiagramWithMorphism:" ++
      "\n the morphism domain differs from the signature in given source node")
                         pos

{- | Build a diagram that extends a given diagram with a node and an
edge from that node. The edge is labelled with a given signature
morphism and the node contains the source of this morphism. Extends
the development graph with the given morphism as well. -}
extendDiagramWithMorphismRev :: Range       -- ^ the position (for diagnostics)
                             -> LogicGraph
                             -> Diag          -- ^ the diagram to be extended
                             -> DGraph        -- ^ the development graph
                             -> DiagNodeSig
                             -- ^ the node to which the edge should point
                             -> GMorphism
                             -- ^ the morphism as label for the new edge
                             -> String -- ^ a diagnostic node description
                             -> DGOrigin      -- ^ the origin of the new node
                             -> Result (DiagNodeSig, Diag, DGraph)
-- ^ returns the new node, the extended diagram and extended development graph
extendDiagramWithMorphismRev pos _ diag dg (Diag_node_sig n nsig)
                             mor desc orig =
  if getSig nsig == cod mor then
     do (sourceSig, dg') <- extendDGraphRev dg nsig mor orig
        let nodeContents = DiagNode {dn_sig = sourceSig, dn_desc = desc}
            diagGr = diagGraph diag
            node = Tree.getNewNode diagGr
            diagGr' = insNode (node, nodeContents) diagGr
            diag' = Diagram{ diagGraph = insEdge (node, n, DiagLink {
                                dl_morphism = mor ,
                                dl_number = numberOfEdges diag + 1}) diagGr',
                              numberOfEdges = numberOfEdges diag + 1 }
        printDiag (Diag_node_sig node sourceSig, diag', dg')
               "extendDiagramWithMorphismRev" diag'
     else fatal_error
     ("Internal error: Static.ArchDiagram.extendDiagramWithMorphismRev:\n" ++
      " the morphism codomain differs from the signature in given target node")
     pos

{- | Build a diagram that extends given diagram with a node containing
given signature and with edge from given nodes to the new node.  The
new edge is labelled with given signature morphism. -}
extendDiagram :: Diag          -- ^ the diagram to be extended
              -> DiagNodeSig   -- ^ the node from which morphism originates
              -> GMorphism     -- ^ the morphism as label for the new edge
              -> NodeSig       -- ^ the signature as label for the new node
              -> String        -- ^ the node description (for diagnostics)
              -> Result (DiagNodeSig, Diag)
-- ^ returns the new node and the extended diagram
extendDiagram diag (Diag_node_sig n _) edgeMorph newNodeSig desc =
  do let nodeContents = DiagNode {dn_sig = newNodeSig, dn_desc = desc}
         diagGr = diagGraph diag
         node = Tree.getNewNode diagGr
         diagGr' = insNode (node, nodeContents) diagGr
         diag' = Diagram{diagGraph = insEdge (n, node, DiagLink {
                             dl_morphism = edgeMorph,
                             dl_number = numberOfEdges diag + 1 }) diagGr',
                         numberOfEdges = numberOfEdges diag + 1 }
         newDiagNode = Diag_node_sig node newNodeSig
     printDiag (newDiagNode, diag') "extendDiagram" diag'

{- | Convert a homogeneous diagram to a simple diagram where all the
signatures in nodes and morphism on the edges are coerced to a common
logic. -}
homogeniseDiagram :: Logic lid sublogics
                           basic_spec sentence symb_items symb_map_items
                           sign morphism symbol raw_symbol proof_tree
                  => lid     -- ^ the target logic to be coerced to
                  -> Diag    -- ^ the diagram to be homogenised
                  -> Result (Tree.Gr sign (Int,morphism))
{- The implementation relies on the representation of graph nodes as
integers. We can therefore just obtain a list of all the labelled
nodes from diag, convert all the nodes and insert them to a new
diagram; then copy all the edges from the original to new diagram
(coercing the morphisms). -}
homogeniseDiagram targetLid diag =
    do let convertNode (n, dn) =
               do G_sign srcLid sig _ <- return $ getSig $ dn_sig dn
                  sig' <- coerceSign srcLid targetLid "" sig
                  return (n, plainSign sig')
           convertEdge (n1, n2, DiagLink {
                   dl_morphism =  GMorphism cid _ _ mor _, dl_number = nr})
               = if isIdComorphism (Comorphism cid) then
                 do mor' <- coerceMorphism (targetLogic cid) targetLid "" mor
                    return (n1, n2, (nr,mor'))
                 else fail $
                  "Trying to coerce a morphism between different logics.\n" ++
                  "Heterogeneous specifications are not fully supported yet."
           convertNodes cDiag [] = do return cDiag
           convertNodes cDiag (lNode : lNodes) =
               do convNode <- convertNode lNode
                  let cDiag' = insNode convNode cDiag
                  convertNodes cDiag' lNodes
           convertEdges cDiag [] = do return cDiag
           convertEdges cDiag (lEdge : lEdges) =
               do convEdge <- convertEdge lEdge
                  let cDiag' = insEdge convEdge cDiag
                  convertEdges cDiag' lEdges
           dNodes = labNodes $ diagGraph diag
           dEdges = labEdges $ diagGraph diag
       -- insert converted nodes to an empty diagram
       cDiag <- convertNodes Graph.empty dNodes
       -- insert converted edges to the diagram containing only nodes
       cDiag' <- convertEdges cDiag dEdges
       return cDiag'

-- | Create a graph containing descriptions of nodes and edges.
diagDesc :: Diag
         -> Tree.Gr String String
diagDesc diag =
    let insNodeDesc g (n, DiagNode { dn_desc = desc }) =
            if desc == "" then g else insNode (n, desc) g
    in foldl insNodeDesc Graph.empty . labNodes $ diagGraph diag

-- | Create a sink consisting of incusion morphisms between
-- signatures from given set of nodes and given signature.
inclusionSink :: LogicGraph
              -> [DiagNodeSig] -- ^ the source nodes
              -> NodeSig       -- ^ the target signature
              -> Result [(Node, GMorphism)]
-- ^ returns the diagram with edges inserted
inclusionSink lgraph srcNodes tnsig =
    do let insmorph ls dns = do
             l <- ls
             case dns of
               Diag_node_sig n nsig -> do
                 incl <- ginclusion lgraph (getSig nsig) (getSig tnsig)
                 return ((n, incl): l)
       sink <- foldl insmorph (return []) srcNodes
       return sink

{- | Build a diagram that extends the given diagram with an
edge between existing nodes.
The edge is labelled with a given signature morphism. Extends the
development graph with the given morphism as well. -}
extendDiagramWithEdge :: Range         -- ^ the position (for diagnostics)
                          -> LogicGraph
                          -> Diag          -- ^ the diagram to be extended
                          -> DGraph        -- ^ the development graph
                          -> DiagNodeSig
                          -- ^ the node from which the edge should originate
                          -> DiagNodeSig
                          -- ^ the target node of the edge
                          -> GMorphism
                          -- ^ the morphism as label for the new edge
                          -> DGLinkOrigin -- ^ the origin of the new edge
                          -> Result (Diag, DGraph)
-- ^ returns the extended diagram and extended development graph
extendDiagramWithEdge pos _ diag dg
                          (Diag_node_sig s ssig)
                          (Diag_node_sig t tsig)
                          mor orig =
  if getSig tsig == cod mor then
   if getSig ssig == dom mor then
     do
        let linkContents = globDefLink mor orig
            s' = getNode ssig
            t' = getNode tsig
            dg' = snd $ insLEdgeDG (s', t', linkContents) dg
            diagGr = diagGraph diag
            diag' = Diagram{diagGraph = insEdge (s, t, DiagLink {
                               dl_morphism = mor,
                               dl_number = numberOfEdges diag + 1 }) diagGr,
                            numberOfEdges = numberOfEdges diag + 1 }
        printDiag (diag', dg')
                      "extendDiagramWithMorphism" diag'
      else fatal_error
     ("Internal error: Static.ArchDiagram.extendDiagramWithMorphism:" ++
      "\n the morphism domain differs from the signature in given source node")
                         pos
   else fatal_error
     ("Internal error: Static.ArchDiagram.extendDiagramWithMorphism:" ++
      "\n the morphism domain differs from the signature in given target node")
                         pos

