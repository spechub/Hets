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

-}

module DevGraph where

import Grothendieck
import Graph
import FiniteMap
import Id

data DGNode = DGNode {
                dgn_sign :: G_sign, -- only the delta
                dgn_sens :: G_l_sentence_list, 
                                -- or better [(String,G_sentence)] ???
                dgn_origin :: DGOrigin
              }   
            | DGRef { 
                dgn_name :: SIMPLE_ID,
                dgn_libname :: SIMPLE_ID, 
                dgn_node :: Node
              }
            
data DGLink = DGLink {
              -- dgl_name :: String,
              -- dgl_src, dgl_tar :: DGNode,  -- already in graph structure
              dgl_morphism :: G_morphism,
              dgl_type :: DGLinkType,
              dgl_origin :: DGOrigin }


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

data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding 
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree 
              | DGLocal | DGClosed 
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec 
              | DGView | DGFitView | DGFitViewImp | DGFitViewA | DGFitViewAImp

type DGraph = Graph DGNode DGLink

type ExtGenSig = (Node,[Node],Node)
type ExtViewSig = (Node,G_morphism,ExtGenSig)
type ArchSig = () -- to be done
type UnitSig = () -- to be done

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig

type GlobalEnv = FiniteMap SIMPLE_ID GlobalEntry

type LibEntry = (GlobalEnv,DGraph)

type LibEnv = FiniteMap SIMPLE_ID LibEntry


get_dgn_name :: DGNode -> Maybe String
