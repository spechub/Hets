{- HetCATS/DevGraph.hs
   $Id$
   Till Mossakowski

   Central data structure for development graphs.

   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from http://www.informatik.uni-bremen.de/~till/calculus.ps

todo:

Integrate stuff from Saarbrücken
GEnv should become superfluous (cf. extended static semantics)
  => annotate nodes and links with their origin
Use graph library
-}

module DevGraph where

import Grothendieck
import Graph

data DGNode = DGNode {
              dgn_name :: String,
              dgn_sign :: G_sign,
              dgn_sens :: [(String,G_sentence)],
              dgn_generated :: Bool }
            
data DGLink = DGLink {
              dgl_name :: String,
              dgl_src, dgl_tar :: DGNode,
              dgl_morphism :: G_morphism,
              dgl_type :: DGLinkType }


data DGLinkType = LocalDef 
            | GlobalDef
            | HidingDef
            | FreeDef
            | LocalThm Bool  -- is_proved
            | GlobalThm Bool  -- is_proved
            | HidingThm G_morphism Bool  -- reduction mor, is_proved
            | FreeThm G_morphism Bool
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2

type DGraph = Graph DGNode DGLink
