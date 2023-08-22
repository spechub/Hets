{-# LANGUAGE RankNTypes #-}
{- |
Module      :  ./Static/ChangeGraph.hs
Description :  functions for changing a development graphs
Copyright   :  (c)  Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

functions to manipulate a development graph for change management

All of the following functions may fail, therefore the result type should
not be taken literally, but maybe changed to some monadic result type.

Also all functions modify an development graph when the are successful, which
may be captured by some form of a state monad.
-}

module Static.ChangeGraph where

import Static.DgUtils
import Static.GTheory
import Static.DevGraph
import Static.History

import Logic.Grothendieck

import Common.AS_Annotation
import Common.Consistency
import qualified Common.OrderedMap as OMap
import Common.Result

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Set as Set
import Data.List

import Control.Monad
import qualified Control.Monad.Fail as Fail

-- * deleting and adding nodes

{- | delete a node.

If a node is deleted all in- and outgoing links will be lost.  This is intended
for ingoing definitions links.  The targets of outgoing definitions links (aka
"depending nodes") need to me marked as "reduced".

theorem links from A to B state that all sentences in A can be proven by the
axioms (and proven theorems) from B (note the reversal). This means the
sentences of A are translated and moved to B as theorems (to be proven) by
"local inference".

removing ingoing theorem links means: we loose properties of B, which is no
problem since we delete B. (If we just delete the theorem link we must inform
depending nodes that fewer axioms are now available. Since a proof for the
link will be lost other proofs in depending nodes may become invalid.)

removing outgoing (local) theorem links means: target nodes may contain theorems
from the source node that need to be deleted, too. So these nodes are
"reduced" (fewer theorems only). (We do not keep even valid theorems, if we
are told to delete them.)

The node to be deleted may have been subject to global decomposition.  So
outgoing global theorems of depending nodes may get a deleted edge-id in
their proof-basis, that should be deleted, too.

Outgoing theorem links of source nodes that have definition links to the
target node to be deleted may be theorem links created by global decomposition
which should be deleted, too.

So, when deleting a node, let's delete the edges in reverse order of their
creation. remove:

  - (outgoing) local theorem links (with reversal of "local-inference")
    whose corresponding global theorem link has only this local theorem link
    as proof basis.

    - sentences in targets are removed (or the target is deleted node anyway)
      (if the local theorem was proven)

    - corresponding global theorem links become unproven again and loose
      their proof basis (or are deleted together with the node)

  - unproven global theorem links (with reversal of "global-decomposition")

    - the proof basis of other proven global theorem links with the same
      target is reduced and marked as incomplete (since a corresponding local
      theorem link and the definition link is not deleted yet).

  - so proven global theorems links are removed after removing the links in
    their proof basis first

  - outgoing definition links

    - target nodes need to be marked as reduced (outgoing global theorem links
      may become complete again)

      (Proofs relying on imported axioms become invalid, provided the sentence
      are still well-formed in the reduced signature)

  - ingoing definition links
    this just marks the current node as reduced which will be deleted later

Later on reduced nodes need to be re-computed possibly causing depending nodes
to become reduced. Incomplete global theorem links need to be completed (by
the user).

If the node index is unknown then auxiliary functions (or a mapping between
node names and node indices) can be supplied to delete nodes by name. -}

deleteDGNode :: Node -> DGraph -> Result DGraph
deleteDGNode t dg = case fst . match t $ dgBody dg of
  Just (ins, _, nl, outs) -> case dgn_nf nl of
    Just n -> do
      dg2 <- deleteDGNode n dg
      deleteDGNode t $ changeDGH dg2 $ SetNodeLab nl
        (t, nl { dgn_nf = Nothing, dgn_sigma = Nothing })
    Nothing -> case dgn_freenf nl of
      Just n -> do
        dg2 <- deleteDGNode n dg
        deleteDGNode t $ changeDGH dg2 $ SetNodeLab nl
          (t, nl { dgn_freenf = Nothing, dgn_phi = Nothing })
      Nothing ->
        if null $ ins ++ outs then return $ changeDGH dg $ DeleteNode (t, nl)
        else do
          dg2 <- foldM (\ dgx (el, sr) -> delDGLink (Just sr) t (dgl_id el) dgx)
            dg ins
          dg3 <- foldM (\ dgx (el, rt) -> delDGLink (Just t) rt (dgl_id el) dgx)
            dg2 outs
          deleteDGNode t dg3
  _ -> justWarn dg $ "node not in graph: " ++ show t

{- | add a node supplying the necessary information.

We should allow to add a node without knowing its final signature. We just
know the 'XNode' information. Later on definition and theorem links may be
added. Only after all ingoing definition links (and their sources) are known
we can compute the actual signature (and theory).

The node index will be new and returned. The name should be unique. The theory
is a closed signature plus local sentences. The origin could be anything (to
be added yet), but for basic specs it is the list of the newly introduced
symbols.

The required conservativity is some value from
`Common.Consistency.Conservativity' like usually 'None' or 'Cons'.

Reference nodes can not be added this way. Also the references and morphisms
to normal forms for hiding or free links cannot be set this way. So further
function are needed. -}

addDGNode :: NodeName -> G_theory -> DGOrigin -> Conservativity -> DGraph
  -> Result (DGraph, Node)
addDGNode nn th o cs dg = let
  n = getNewNodeDG dg
  inf = newConsNodeInfo o cs
  sn = showName nn
  nl = newInfoNodeLab nn inf th
  in case lookupNodeByName sn dg of
     [] -> return (changeDGH dg $ InsertNode (n, nl), n)
     ns -> Fail.fail $ "node name '" ++ sn
       ++ "' already defined in graph for node(s): "
       ++ show (map fst ns)

-- | Maybe a function to rename nodes is desirable
renameNode :: Node -> NodeName -> DGraph -> Result DGraph
renameNode n nn dg = let
  sn = showName nn
  nl = labDG dg n
  in case lookupNodeByName sn dg of
     [] -> return $ changeDGH dg $ SetNodeLab nl (n, nl { dgn_name = nn })
     ns -> Fail.fail $ "node name '" ++ sn
       ++ "' already defined in graph for node(s): "
       ++ show (map fst ns)

-- * deleting and adding links

{- | delete a link given the source and target node by index and the edge-id.

Edge-ids are globally unique, but locating source and target nodes would be
inefficient if not given.

Getting the edge-id if only source node name, target
node name, link type, possibly an origin, and the link morphism is given,
needs auxiliary functions.

Edge-ids maybe reused.

Local theorem links are proven by moving sentences from the source to target
node and changing them to theorems. So if such a proven local theorem link is
removed the target node needs to be reduced, too.

target nodes of definition links are "reduced" (see deleteDGNode)

-}

delDGLink :: Maybe Node -> Node -> EdgeId -> DGraph -> Result DGraph
delDGLink ms t i dg = let
  (ins, _, nl, loopsAndOuts) = safeContextDG "delDGLink" dg t
  loops = filter ((== t) . snd) loopsAndOuts
  allIns = loops ++ ins
  in case partition ((== i) . dgl_id . fst) allIns of
    ([], _) -> justWarn dg $ "link not found: " ++ show (t, i)
    ((lbl, s) : os, rs) -> do
     unless (null os) $ justWarn ()
       $ "ambiguous link: " ++ shows (t, i) " other sources are: "
         ++ show (map snd os)
     case ms of
      Just sr | sr /= s -> Fail.fail
        $ "non-matching source node: " ++ show (s, t, i)
        ++ " given: " ++ show sr
      _ -> let delE dg' = return $ changeDGH dg' $ DeleteEdge (s, t, lbl)
               -- links proven by current link
               gs = filter (edgeInProofBasis i . getProofBasis . fst) rs
               dgCh = changeDGH dg $ SetNodeLab nl (t, updNodeMod delSymMod nl)
               delDef = delE dgCh
       in case dgl_type lbl of
       ScopedLink lOrG lk _ -> case lOrG of
         Local -> do
           dg2 <- case lk of
                 ThmLink (Proven (DGRuleLocalInference renms) _) -> do
                   nl2 <- deleteDGNodeSens (\ nSen -> not (isAxiom nSen)
                     && senAttr nSen `elem` map snd renms) nl
                   return $ updDGNodeLab dg nl (t, nl2)
                 _ -> return dg
           -- find global link(s) that contain(s) the edge-id as proof-basis
           let dg3 = invalDGLinkProofs dg2 $ map (\ (l, sr) -> (sr, t, l)) gs
           delE dg3
         Global -> case lk of
           ThmLink pst -> let
             pB = proofBasisOfThmLinkStatus pst
             {- delete all links created by global decomposition,
             (this may delete also manually inserted theorem links!)
             all links have the same target. -}
             createdLinks =
               filter ((`edgeInProofBasis` pB) . dgl_id . fst) rs
             in if null createdLinks then
                  let dg3 = invalDGLinkProofs dg
                            $ map (\ (l, sr) -> (sr, t, l)) gs
                  in delE dg3
                else do
                   dg2 <- foldM (\ dgx (el, sr) ->
                        delDGLink (Just sr) t (dgl_id el) dgx) dg createdLinks
                   delDGLink ms t i dg2
           DefLink -> delDef
       HidingFreeOrCofreeThm {} -> delE dg
           {- just delete the theorem link, we don't know what links can be
           in the proof basis by the shifting rules -}
       _ -> delDef          -- delete other def links

updNodeMod :: NodeMod -> DGNodeLab -> DGNodeLab
updNodeMod m nl = nl { nodeMod = mergeNodeMod m $ nodeMod nl }

updDGNodeLab :: DGraph
  -> DGNodeLab -- ^ old label
  -> LNode DGNodeLab -- ^ node with new label
  -> DGraph
updDGNodeLab dg l n = let
    dg0 = changeDGH dg $ SetNodeLab l n
    in togglePending dg0 $ changedLocalTheorems dg0 n

deleteDGNodeSens :: (forall a . Named a -> Bool) -> DGNodeLab
  -> Result DGNodeLab
deleteDGNodeSens p nl = case dgn_theory nl of
  G_theory lid s si sens _ ->
    case OMap.partitionWithKey (\ n -> p . reName (const n)) sens of
      (del, rest) -> let
          es = OMap.elems del
          chg | all isAxiom es = delAxMod
              | all (not . isAxiom) es = delThMod
              | otherwise = delSenMod
        in if OMap.null del
          then justWarn nl $ "no sentence deleted in: " ++ getDGNodeName nl
          else return $ updNodeMod chg $ nl
            { dgn_theory = G_theory lid s si rest startThId }

invalidateDGLinkProof :: DGLinkLab -> DGLinkLab
invalidateDGLinkProof el = el { dgl_type = setProof LeftOpen $ dgl_type el }

invalDGLinkProof :: LEdge DGLinkLab -> [DGChange]
invalDGLinkProof e@(s, t, l) =
  [DeleteEdge e, InsertEdge (s, t, invalidateDGLinkProof l)]

invalDGLinkProofs :: DGraph -> [LEdge DGLinkLab] -> DGraph
invalDGLinkProofs dg = changesDGH dg . concatMap invalDGLinkProof

{- | add a link supplying the necessary information.

Morphisms do not store source and target signatures. Only the source signature
is taken from the node. The induced signature of the morphism will be a
subsignature of the target signature.

- adding an (unproven) global theorem link:

  this states that more theorems are supposed to hold in target nodes.

- adding a global definition link:

  - the signature of the target is enlarged (Proofs remain valid).

  - proven outgoing global theorem links for new ingoing definition links may
    become unproven and incomplete

  - outgoing local theorem links for new ingoing definition links add proof
    obligations the target nodes of the local theorem links.
    Additional theorems need to be moved or we mark the proven local theorem
    link as incomplete.

The link type may also contain a conservativity and isn't easy to set up for
free and hiding links. The origin is again basically for documentation
purposes.

The returned edge-id will be new or an edge-id may be supplied as input. -}

addDGLink :: Node -> Node -> GMorphism -> DGLinkType -> DGLinkOrigin -> DGraph
  -> (DGraph, EdgeId)
addDGLink = undefined

-- * modifying links

{- | Do we need functions to modify links?

Yes, later, for example, if a conservativity as part of the link type should
be set or changed.

Some link types contain proof information that needs to be kept up-to-date.

For example, a global theorem link will (after decomposition) refer to a local
theorem link and maybe another global theorem link. A local theorem link will
(after local inference) refer to (possibly renamed) theorems in the target
node.

Maybe some more thoughts are needed to decide which link type information may
be set or changed explicitely and which information should be adjusted
automatically. -}

modifyDGLinkType :: Node -> Node -> EdgeId -> DGLinkType -> DGraph -> DGraph
modifyDGLinkType = undefined

{- |
If the link morphism should change, this most likely (but not necessarily)
involves signature changes of the source or target node (or both nodes).

In the latter case, either the old link was invalidated before, by changing
the signature of the source or target node, or the modification of the link
will invalidate the contents of the source or target.

Instead of tricky morphism changes it may be better to simply delete old edges
and nodes and reinsert new nodes and edges propagating some old attributes. -}

modifyDGLinkMorphism :: Node -> Node -> EdgeId -> GMorphism -> DGraph -> DGraph
modifyDGLinkMorphism = undefined

-- | Modifying the documenting link origin should also be possible.
modifyDGLinkOrigin :: Node -> Node -> EdgeId -> DGLinkOrigin -> DGraph -> DGraph
modifyDGLinkOrigin = undefined

-- * modifying the signature of a node

{- | replace the signature of a node.

This function should be used as basis to add or delete symbols from a node.

Changing the signature means that the codomain of incoming and the domain of
outgoing links change. Therefore we would invalidate all attached links and
expect further link morphism modifications to adjust these links.

If the signature is not enlarged some local sentences may become invalid.
Therefore the class logic must supply a checking function that takes a
signature and a sentence and checks if the sentence is still well-formed
according to the given signature. A logic specific implementation my choose to
first extract all symbols from a sentence and compare it to the set of
signature symbols. (Extracting symbols from sentences is no method of the
class logic.)

Since there are functions to remove sentences explicitely, we leave it to the
user to remove sentences first before reducing or changing the signature and
simply fail if invalid sentences are left! -}

setSignature :: Node -> G_sign -> DGraph -> DGraph
setSignature = undefined

{- | delete symbols from a node's signature.

Deleting symbols is a special case of setting a node's signature. The new
signature is computed using the method for the co-generated signature that is
also used when symbols are hidden.

It is only checked that the symbol set difference of the new and old signature
corresponds to the supplied symbol set. (Alternatively it could be checked if
the new signature is a sub-signature of the old one.)

The target nodes of outgoing definition links will be adjusted according to
the reduced closed signature automatically.

Invalid sentences should have been removed before.

This function can be easily extended to delete raw symbol via the logic
specific matching between raw and signature symbols. -}

deleteSymbols :: Node -> Set.Set G_symbol -> DGraph -> DGraph
deleteSymbols = undefined

{- | extending a node's signature.

Adding symbols requires the new signature directly supplied as argument, since
the class logic supplies no way to extend a signature by a given set of
symbols. In fact symbols can only be extracted from a given signature.

It is only checked if the old signature is a sub-signature of the new one.

Sentences are not checked, because fully analyzed sentences are expected to
remain well-formed in an enlarged signature, although re-parsing and
type-checking may fail for the syntactic representation of these sentences.

It is, however, possible to extend a given signature by a basic spec as
happens for usual spec extensions, but note that the basic analysis may also
yield sentences that might need to be added separately.

Again target nodes of outgoing definition links will be adjusted
automatically. -}

extendSignature :: Node -> G_sign -> DGraph -> DGraph
extendSignature = undefined

-- * modifying local sentences of a node

{- | a logic independent sentence data type, yet missing in Logic.Grothendieck

Local sentences have been either directly added or have been inserted by
local inference. Sentences inserted by local inference should not be
manipulated at the target node but only at the original source. But maybe it
should be possible to delete such sentences explicitly to match the
corresponding deletion of the proven local theorem link? Alternatively a
function to undo a local inference step could be applied.

All sentences are uniquely named. User given duplicate names or missing names
are removed by generating unique names.

If additional sentences are added by local inference they may be
renamed to ensure unique names. The renaming is stored to keep the
correspondence to the original sentences.

The global theory of node should be computed if needed but is cached for
efficiency reason. It contains all sentences as axioms along incoming
definition links. All these axioms may be used to prove a theorem, assuming
that the used axioms are valid in their original theory.

So a change of a sentence may invalidate proofs in nodes reachable via theorem
or definition links. -}

data GSentence = GSentence

{- | delete the sentences that fulfill the given predicate.

Should this function fail if the predicate does not determine a unique
sentence?  Surely, simply all sentences could be deleted fulfilling the
predicate (possibly none). -}

deleteSentence :: Node -> (Named GSentence -> Bool) -> DGraph -> Result DGraph
deleteSentence = undefined

{- | delete a sentence by name

This is a more efficient version of deleting a single sentence. All sentences
of one node have a unique name, but it may be a generated name that the user
needs to look up.

Only sentences not inserted by local inference can be deleted.
-}

deleteSentenceByName :: Node -> String -> DGraph -> DGraph
deleteSentenceByName = undefined

{- | add a sentence.

The unproven named sentence given as argument is added as new sentence. The
name must be different from those of all other sentences, including those
inserted by local inference.

Adding axioms will not invalidate proofs (if the logic is monotone), but the
addition may trigger the addition of theorems in a neighbor node if linked to
via a proven local theorem link.  Theorems are not propagated further.

Sentences can not be added with some old proof, that could be retried by the
corresponding prover. -}

addSentence :: Node -> Named GSentence -> DGraph -> DGraph
addSentence = undefined

{- | It may be desirable to rename sentences or change there role (axiom or
theorem) and even to invalid but keep an old proof. -}

changeSentence :: Node -> (Named GSentence -> Named GSentence) -> DGraph
  -> DGraph
changeSentence = undefined
