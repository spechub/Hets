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

import Common.Consistency

import Data.Graph.Inductive.Graph as Graph

-- * adding or deleting nodes or links

{- All of the following functions may fail, therefore the result type should
not be taken literally, but maybe changed to some monadic result type.

Also all functions modify an development graph, if the are successful, which
may be captured by a some form of a state monad.
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

Deleted edge-ids are never reused. -}

deleteDGLink :: Node -> Node -> EdgeId -> DGraph -> DGraph
deleteDGLink = undefined

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

-- * modifying nodes

{-
the following operations would change a given Node:
   add, delete symbols
   add, delete, rename, modify sentences

how about renaming nodes.
-}





