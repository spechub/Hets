{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

{-
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
Should AS be stored in GloblaContext as well?
-}

module Static.DevGraph where

import Logic.Logic
import Logic.Grothendieck
import Syntax.AS_Library
import Common.GlobalAnnotations

import Common.Lib.Graph as Graph
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.PrettyPrint
import Common.PPUtils
import Common.Result
import Common.Lib.Pretty


-- * Types for structured specification analysis

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???
data DGNodeLab = DGNode {
                dgn_name :: Maybe SIMPLE_ID,
                dgn_sign :: G_sign, 
                dgn_sens :: G_l_sentence_list, 
                dgn_origin :: DGOrigin
              }   
            | DGRef { 
                dgn_renamed :: Maybe SIMPLE_ID,
                dgn_libname :: LIB_NAME, 
                dgn_node :: Node
              } deriving (Show,Eq)

isDGRef :: DGNodeLab -> Bool
isDGRef (DGNode _ _ _ _) = False
isDGRef (DGRef _ _ _) = True

locallyEmpty ::  DGNodeLab -> Bool
locallyEmpty (DGNode _ (G_sign lid sigma) (G_l_sentence_list _ sens) _) = 
  is_subsig lid sigma (empty_signature lid) && null sens
locallyEmpty (DGRef _ _ _) = True
           
data DGLinkLab = DGLink {
              -- dgl_name :: String,
              -- dgl_src, dgl_tar :: DGNodeLab,  -- already in graph structure
              dgl_morphism :: GMorphism,
              dgl_type :: DGLinkType,
              dgl_origin :: DGOrigin }
              deriving (Eq,Show)

instance PrettyPrint DGLinkLab where
  printText0 ga l = printText0 ga (dgl_morphism l)
                    <+> ptext (show (dgl_type l))
                    <+> printText0 ga (dgl_origin l)

data ThmLinkStatus =  Open | Proven [DGLinkLab] deriving (Eq, Show)

data DGLinkType = LocalDef 
            | GlobalDef
            | HidingDef
            | FreeDef NodeSig -- the "parameter" node
            | CofreeDef NodeSig -- the "parameter" node
	    | LocalThm ThmLinkStatus Conservativity ThmLinkStatus
               -- ??? Some more proof information is needed here
               -- (proof tree, ...)
	    | GlobalThm ThmLinkStatus Conservativity ThmLinkStatus
	    | HidingThm GMorphism ThmLinkStatus
            | FreeThm GMorphism Bool
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2
              deriving (Eq,Show)

data Conservativity = None | Cons | Mono | Def
              deriving (Eq,Show,Ord)

data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding 
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree 
              | DGLocal | DGClosed | DGClosedLenv | DGLogicQual | DGLogicQualLenv 
              | DGData
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec 
              | DGView SIMPLE_ID | DGFitView SIMPLE_ID | DGFitViewImp SIMPLE_ID
              | DGFitViewA SIMPLE_ID | DGFitViewAImp SIMPLE_ID | DGProof
              deriving (Eq,Show)

type DGraph = Graph DGNodeLab DGLinkLab

data NodeSig = NodeSig (Node,G_sign) | EmptyNode AnyLogic
               deriving (Eq,Show)

instance PrettyPrint NodeSig where
  printText0 ga (EmptyNode _) = ptext "<empty NodeSig>"
  printText0 ga (NodeSig(n,sig)) = 
    ptext "node" <+> printText0 ga n <> ptext ":" <> printText0 ga sig

getNode (NodeSig (n,sigma)) = Just n
getNode (EmptyNode _) = Nothing

emptyG_sign :: AnyLogic -> G_sign
emptyG_sign (Logic lid) = G_sign lid (empty_signature lid)

getSig (NodeSig (n,sigma)) = sigma
getSig (EmptyNode l) = emptyG_sign l

getNodeAndSig (NodeSig (n,sigma)) = Just (n,sigma)
getNodeAndSig (EmptyNode _) = Nothing

getLogic (NodeSig (n,G_sign lid _)) = Logic lid
getLogic (EmptyNode l) = l

-- | Create a node that represents a union of signatures
nodeSigUnion :: LogicGraph -> DGraph -> [NodeSig] -> DGOrigin -> Result (NodeSig, DGraph)
nodeSigUnion lgraph dg nodeSigs orig =
  do sigUnion@(G_sign lid _) <- gsigManyUnion lgraph (map getSig nodeSigs)
     let nodeContents = DGNode {dgn_name = Nothing,
				dgn_sign = sigUnion,
				dgn_sens = G_l_sentence_list lid [],
				dgn_origin = orig }
	 [node] = newNodes 0 dg
	 dg' = insNode (node, nodeContents) dg
	 inslink dgres nsig = do dg <- dgres
				 case getNode nsig of
				      Nothing -> return dg
				      Just n -> do incl <- ginclusion lgraph (getSig nsig) sigUnion
						   return (insEdge (n, node, DGLink {dgl_morphism = incl,
										     dgl_type = GlobalDef,
										     dgl_origin = orig }) dg)
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig (node, sigUnion), dg'')

-- | Extend the development graph with given morphism originating
-- from given NodeSig
extendDGraph :: DGraph    -- ^ the development graph to be extended
	     -> NodeSig   -- ^ the NodeSig from which the morphism originates
	     -> GMorphism -- ^ the morphism to be inserted
	     -> DGOrigin  
	     -> Result (NodeSig, DGraph)
-- ^ returns 1. the target signature of the morphism and 2. the resulting DGraph
extendDGraph _ n@(EmptyNode _) _ _ =
    do fail "Internal error: \
             \trying to add a morphism originating from an empty node"
extendDGraph dg (NodeSig (n, G_sign lid _)) morph orig =
    let targetSig = cod Grothendieck morph
        nodeContents = DGNode {dgn_name = Nothing,
			       dgn_sign = targetSig,
			       dgn_sens = G_l_sentence_list lid [],			       
			       dgn_origin = orig}
	linkContents = DGLink {dgl_morphism = morph,
			       dgl_type = GlobalDef, -- TODO: other type
			       dgl_origin = orig}
	[node] = newNodes 0 dg
	dg' = insNode (node, nodeContents) dg
	dg'' = insEdge (n, node, linkContents) dg'
    in do return (NodeSig (node, targetSig), dg'')


-- | Extend the development graph with given morphism pointing to 
-- given NodeSig
extendDGraphRev :: DGraph    -- ^ the development graph to be extended
	     -> NodeSig   -- ^ the NodeSig to which the morphism points
	     -> GMorphism -- ^ the morphism to be inserted
	     -> DGOrigin  
	     -> Result (NodeSig, DGraph)
-- ^ returns 1. the source signature of the morphism and 2. the resulting DGraph
extendDGraphRev _ n@(EmptyNode _) _ _ =
    do fail "Internal error: \
             \trying to add a morphism pointing to an empty node"
extendDGraphRev dg (NodeSig (n, G_sign lid _)) morph orig =
    let sourceSig = dom Grothendieck morph
        nodeContents = DGNode {dgn_name = Nothing,
			       dgn_sign = sourceSig,
			       dgn_sens = G_l_sentence_list lid [],			       
			       dgn_origin = orig}
	linkContents = DGLink {dgl_morphism = morph,
			       dgl_type = GlobalDef, -- TODO: other type
			       dgl_origin = orig}
	[node] = newNodes 0 dg
	dg' = insNode (node, nodeContents) dg
	dg'' = insEdge (node, n, linkContents) dg'
    in do return (NodeSig (node, sourceSig), dg'')


data ExtNodeSig = ExtNodeSig (Node,G_ext_sign) | ExtEmptyNode AnyLogic
               deriving (Eq,Show)

instance PrettyPrint ExtNodeSig where
  printText0 ga (ExtEmptyNode _) = ptext "<empty NodeSig>"
  printText0 ga (ExtNodeSig(n,sig)) = 
    ptext "node" <+> printText0 ga n <> ptext ":" <> printText0 ga sig

getExtNode (NodeSig (n,sigma)) = Just n
getExtNode (EmptyNode _) = Nothing

getExtSig (ExtNodeSig (n,sigma)) = sigma
getExtSig (ExtEmptyNode (Logic lid)) = 
  G_ext_sign lid (empty_signature lid) Set.empty

getExtNodeAndSig (ExtNodeSig (n,sigma)) = Just (n,sigma)
getExtNodeAndSig (ExtEmptyNode _) = Nothing

getExtLogic (ExtNodeSig (_,G_ext_sign lid _ _)) = Logic lid
getExtLogic (ExtEmptyNode l) = l

-- import, formal parameters, united signature of formal params, body
type ExtGenSig = (NodeSig,[NodeSig],G_sign,NodeSig)

-- source, morphism, parameterized target
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)


-- * Types for architectural and unit specification analysis
-- (as defined for basic static semantics in Chap. III:5.1)

type ParUnitSig = ([NodeSig], NodeSig)

data UnitSig = Unit_sig NodeSig
	     | Par_unit_sig ParUnitSig 
	       deriving (Show, Eq)
emptyUnitSig :: AnyLogic -> UnitSig
emptyUnitSig l = Unit_sig (EmptyNode l)

type ImpUnitSig = (NodeSig, UnitSig)
data ImpUnitSigOrSig = Imp_unit_sig ImpUnitSig 
		     | Sig NodeSig
		       deriving (Show, Eq)

type StUnitCtx = Map.Map SIMPLE_ID ImpUnitSigOrSig
emptyStUnitCtx :: StUnitCtx
emptyStUnitCtx = Map.empty

type ArchSig = (StUnitCtx, UnitSig)


-- * Types for global and library environments

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig 
                 | RefEntry deriving (Show,Eq)

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

type GlobalContext = (GlobalAnnos,GlobalEnv,DGraph)

type LibEnv = Map.Map LIB_NAME GlobalContext


emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

get_dgn_name :: DGNodeLab -> Maybe SIMPLE_ID
get_dgn_name (DGNode (Just name) _ _ _) = Just name
get_dgn_name (DGRef (Just name) _ _) = Just name
get_dgn_name _ = Nothing

instance PrettyPrint DGOrigin where
  printText0 _ origin = case origin of
     DGBasic -> ptext "basic specification"
     DGExtension -> ptext "extension"
     DGTranslation -> ptext "translation"
     DGUnion -> ptext "union"
     DGHiding -> ptext "hiding"
     DGRevealing -> ptext "revealing"
     DGRevealTranslation -> ptext "translation part of a revealing"
     DGFree -> ptext "free specification"
     DGCofree -> ptext "cofree specification"
     DGLocal -> ptext "local specification"
     DGClosed -> ptext "closed specification"
     DGClosedLenv -> ptext "closed specification (inclusion of local environment)"
     DGFormalParams -> ptext "formal parameters of a generic specification"
     DGImports -> ptext "imports of a generic specification"
     DGSpecInst n -> ptext ("instantiation of "++showPretty n "")
     DGFitSpec -> ptext "fittig specification"
     DGView n -> ptext ("view "++showPretty n "")
     DGFitView n -> ptext ("fitting view "++showPretty n "")
     DGFitViewImp n -> ptext ("fitting view (imports) "++showPretty n "")
     DGFitViewA n -> ptext ("fitting view (actual parameters) "++showPretty n "")
     DGFitViewAImp n -> ptext ("fitting view (imports and actual parameters) "++showPretty n "")
     DGProof -> ptext "constructed within a proof"
