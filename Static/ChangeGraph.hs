{- |
Module      :  $Header$
Description :  functions for changing a development graphs
Copyright   :  (c)  Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

functions to manipulate a development graph for change management
-}

module Static.ChangeGraph where

import Static.GTheory
import Static.DevGraph

import Logic.Grothendieck

import Common.AS_Annotation
import Common.Consistency

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Set as Set

-- * adding or deleting nodes or links

{- All of the following functions may fail, therefore the result type should
not be taken literally, but maybe changed to some monadic result type.

Also all functions modify an development graph when the are successful, which
may be captured by some form of a state monad.
-}

{- | delete a node by index.

The node will only be marked as deleted until a final commit.

If the node index is unknown then auxiliary functions (or a mapping between
node names and node indices) can be supplied to delete nodes by name. -}

deleteDGNode :: Node -> DGraph -> DGraph
deleteDGNode = undefined

{- | add a node supplying the necessary information.

The node index will be new and returned. The name should be unique. The theory
is a closed signature plus local sentences. The origin could be anything (to
be added yet), but for basic specs it is the list of the newly introduced
symbols.

The required conservativity is some value from
`Common.Consistency.Conservativity' like usually 'None' or 'Cons'.

Reference nodes can not be added this way. -}

addDGNode :: NodeName -> G_theory -> DGOrigin -> Conservativity -> DGraph
  -> (DGraph, Node)
addDGNode = undefined

{- | delete a link given the source and target node by index and the edge-id.

Edge-ids are globally unique, but locating source and target nodes would be
inefficient if not given.

Getting the edge-id if only source node name, target
node name, link type, possibly an origin, and the link morphism is given,
needs auxiliary functions.

Deleted edge-ids are never reused.

Local theorem links are proven by moving sentences from the source to target
node and changing them to theorems. So if such a proven local theorem link is
removed the target node needs to be adjusted, too. Should this happen
automatically? -}

deleteDGLink :: Node -> Node -> EdgeId -> DGraph -> DGraph
deleteDGLink = undefined

{- | Maybe a function to rename nodes is desirable -}
renameNode :: Node -> NodeName -> DGraph -> DGraph
renameNode = undefined

{- | add a link supplying the necessary information.

The domain and codomain of the morphism must correspond to the signatures
given in the source and target node.

The link type may also contain a conservativity and isn't easy to set up for
free and hiding links. The origin is again basically for documentation
purposes.

The return edge-id will be new.  -}

addDGLink :: Node -> Node -> GMorphism -> DGLinkType -> DGLinkOrigin -> DGraph
  -> (DGraph, EdgeId)
addDGLink = undefined

-- * modifying links

{- | Do we need function to modify links?

Yes, for example, if a conservativity as part of the link type should be set
or changed.

Some link types contain proof information that needs to be kept up-to-date.

For example, a global theorem link will (after decomposition) refer to a local
theorem link and maybe another global theorem link. A local theorem link will
(after local inference) refer to (possibly renamed) theorems in the target
node.

Maybe some more thoughts are needed to decide which link type information may
be set or changed explicitely and which information should be adjusted
automatically.  -}

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

Should the function fail or silently remove invalid sentences? Since there are
functions to remove sentences explicitely, we leave it to the user to remove
sentences first before reducing or changing the signature and simply fail if
invalid sentences are left.  -}

setSignature :: Node -> G_sign -> DGraph -> DGraph
setSignature = undefined
{- | delete symbols from a node's signature.

Deleting symbols is a special case of setting a node's signature. The new
signature is computed using the method for the co-generated signature that is
also used when symbols are hidden.

It is only checked that the symbol set difference of the new and old signature
corresponds to the supplied symbol set. (Alternatively it could be checked if
the new signature is a sub-signature of the old one.)

Invalid sentences will be treated as above when setting a signature.

This function can be easily extended to delete raw symbol via the logic
specific matching between raw and signature symbols.  -}

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
yield sentences that might need to be added separately.  -}

extendSignature :: Node -> G_sign -> DGraph -> DGraph
extendSignature = undefined

-- * modifying local sentences of a node

{- Local sentences have been either directly added or have been inserted by
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
or definition links.  -}

-- any sentence data type, yet missing in Logic.Grothendieck
data GSentence

{- | delete the sentence that fulfills the given predicate.

Should this function fail if the predicate does not determine a unique
sentence?  Surely, simply all sentences could be deleted fulfilling the
predicate (possibly none). -}

deleteSentence :: Node -> (Named GSentence -> Bool) -> DGraph -> DGraph
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
