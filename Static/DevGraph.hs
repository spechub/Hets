{- HetCATS/ Static/DevGraph.hs
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
   CASL Proof calculus. In: CASL reference manual, part IV.
   Available from http://www.cofi.info

todo:

Integrate stuff from Saarbrücken
-}

module Static.DevGraph where

import Logic.Logic
import Logic.Grothendieck
import Syntax.AS_Library
import Common.GlobalAnnotations

import Common.Lib.Graph as Graph
import Common.Lib.Map as Map
import Common.Id

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???
data DGNodeLab = DGNode {
                dgn_name :: Maybe SIMPLE_ID,
                dgn_sign :: G_sign, -- only the delta
                dgn_sens :: G_l_sentence_list, 
                                -- or better [(String,G_sentence)] ???
                dgn_origin :: DGOrigin
              }   
            | DGRef { 
                dgn_renamed :: Maybe SIMPLE_ID,
                dgn_libname :: LIB_NAME, 
                dgn_node :: Node
              }

isDGRef :: DGNodeLab -> Bool
isDGRef (DGNode _ _ _ _) = False
isDGRef (DGRef _ _ _) = True

locallyEmpty ::  DGNodeLab -> Bool
locallyEmpty (DGNode _ (G_sign lid sigma) (G_l_sentence _ sens) _) = 
  sigma == empty_signature lid && null sens
locallyEmpty (DGRef _ _ _) = True
           
data DGLinkLab = DGLink {
              -- dgl_name :: String,
              -- dgl_src, dgl_tar :: DGNodeLab,  -- already in graph structure
              dgl_morphism :: GMorphism,
              dgl_type :: DGLinkType,
              dgl_origin :: DGOrigin }
              deriving (Eq,Show)


data DGLinkType = LocalDef 
            | GlobalDef
            | HidingDef
            | FreeDef NodeSig -- the "parameter" node
            | CofreeDef NodeSig -- the "parameter" node
            | LocalThm Bool Conservativity -- is_proved
               -- ??? Some more proof information is needed here
               -- (proof tree, ...)
            | GlobalThm Bool Conservativity -- is_proved
            | HidingThm GMorphism Bool  -- reduction mor, is_proved
            | FreeThm GMorphism Bool
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2
              deriving (Eq,Show)

data Conservativity = None | Cons | Mono | Def
              deriving (Eq,Show)

data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding 
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree 
              | DGLocal | DGClosed | DGClosedLenv 
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec 
              | DGView SIMPLE_ID | DGFitView | DGFitViewImp 
              | DGFitViewA | DGFitViewAImp | DGProof
              deriving (Eq,Show)

type DGraph = Graph DGNodeLab DGLinkLab

data NodeSig = NodeSig (Node,G_sign) | EmptyNode AnyLogic
               deriving (Eq,Show)

getNode (NodeSig (n,sigma)) = Just n
getNode (EmptyNode _) = Nothing

getSig (NodeSig (n,sigma)) = sigma
getSig (EmptyNode (Logic lid)) = G_sign lid (empty_signature lid)

getNodeAndSig (NodeSig (n,sigma)) = Just (n,sigma)
getNodeAndSig (EmptyNode _) = Nothing

getLogic (NodeSig (n,G_sign lid _)) = Logic lid
getLogic (EmptyNode l) = l

-- import, formal parameters, united signature of formal params, body
type ExtGenSig = (NodeSig,[NodeSig],G_sign,NodeSig)
-- source, morphism, parameterized target
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)
type ArchSig = () -- to be done
type UnitSig = () -- to be done

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig

type GlobalEnv = Map SIMPLE_ID GlobalEntry

type GlobalContext = (GlobalAnnos,GlobalEnv,DGraph)

type LibEnv = Map LIB_NAME GlobalContext


emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

get_dgn_name :: DGNodeLab -> Maybe SIMPLE_ID
get_dgn_name (DGNode (Just name) _ _ _) = Just name
get_dgn_name (DGRef (Just name) _ _) = Just name
get_dgn_name _ = Nothing

