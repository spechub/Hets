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

import Logic.Logic
import Logic.ExtSign
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree
import qualified Common.Lib.SizedList as SizedList
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.LibName
import Common.Consistency

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Query.DFS
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

{- | delete a node by index.
The node will only be marked as deleted until a final commit.
If the node index is unknown auxiliary functions (or a mapping between node
names and node indices) can be supplied to delete nodes by name. -}
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

{- |
add a link supplying the necessary information.
The domain and codomain of the morphism must correspond to the signatures
given in the source and target node.
The link type may also contain a conservativity and isn't easy to set up for
free and hiding links. The origin is again basically for documentation
purposes.
The return edge-id will be new.  -}
addDGLink :: Node -> Node -> GMorphism -> DGLinkType -> DGLinkOrigin -> DGraph
  -> (DGraph, EdgeId)
addDGLink = undefined

{- missing:
   modifyDGLink (change morphism or other attributes)
the following operations would change a given Node:
   add, delete symbols
   add, delete, rename, modify sentences
-}





