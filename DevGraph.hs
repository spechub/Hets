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

import Logic
import Grothendieck
import AS_Library
import GlobalAnnotations

import Graph
import FiniteMap
import Id

data DGNode = DGNode {
                dgn_name :: Maybe SIMPLE_ID,
                dgn_sign :: G_sign, -- only the delta
                dgn_sens :: G_l_sentence_list, 
                                -- or better [(String,G_sentence)] ???
                dgn_origin :: DGOrigin
              }   
            | DGRef { 
                dgn_renamed :: SIMPLE_ID,
                dgn_libname :: LIB_NAME, 
                dgn_node :: Node
              }

isDGRef :: DGNode -> Bool
isDGRef (DGNode _ _ _ _) = False
isDGRef (DGRef _ _ _) = True
            
data DGLink = DGLink {
              -- dgl_name :: String,
              -- dgl_src, dgl_tar :: DGNode,  -- already in graph structure
              dgl_morphism :: GMorphism,
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
              deriving (Eq,Show)

type DGraph = Graph DGNode DGLink

data NodeSig = NodeSig (Node,G_sign) | EmptyNode AnyLogic

getNode (NodeSig (n,sigma)) = Just n
getNode (EmptyNode _) = Nothing

getSig (NodeSig (n,sigma)) = sigma
getSig (EmptyNode (Logic lid)) = G_sign lid (empty_signature lid)

getLogic (NodeSig (n,G_sign lid _)) = Logic lid
getLogic (EmptyNode l) = l

type ExtGenSig = (NodeSig,[NodeSig],NodeSig)
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)
type ArchSig = () -- to be done
type UnitSig = () -- to be done

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig

type GlobalEnv = FiniteMap SIMPLE_ID GlobalEntry

type LibEntry = (GlobalEnv,DGraph,GlobalAnnos)

type LibEnv = FiniteMap LIB_NAME LibEntry

emptyLibEnv :: LibEnv
emptyLibEnv = emptyFM

get_dgn_name :: DGNode -> Maybe SIMPLE_ID
get_dgn_name (DGNode (Just name) _ _ _) = Just name
get_dgn_name (DGRef name _ _) = Just name
get_dgn_name _ = Nothing