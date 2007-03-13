{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Central datastructures for development graphs
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

-}

module Static.DevGraph where

import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover
import Logic.Coerce

import Syntax.AS_Library

import Data.Graph.Inductive.Graph as Graph
import qualified Common.Lib.Graph as Tree

import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result
import Data.Typeable

import Control.Monad (foldM)
import Control.Exception
import Data.Char (toLower)
import Data.List(nub, intersect)

getNewNode :: Tree.Gr a b -> Node
getNewNode g = case newNodes 1 g of
               [n] -> n
               _ -> error "Static.DevGraph.getNewNode"

getNewEdgeIDs :: Int -> DGraph -> [Int]
getNewEdgeIDs count g = take count [maxIDBound..]
		        where
			ids = concat $ map (\(_, _, l) -> dgl_id l) $ labEdges g
			maxIDBound = if null ids then 0
				     else (maximum ids)+1
{-
getNewEdgeIDs count g = getAvailableID count 0 sortedIDs
			where
			ids = map (\(_, _, l) -> dgl_id l) $ labEdges g
			sortedIDs = sort $ concat ids
			getAvailableID :: Int -> Int -> [Int] -> [Int]
			getAvailableID 0 _ _ = []
			getAvailableID c n [] = take c [n..]
			getAvailableID c n (x:xs) 
			   | n==x = getAvailableID c (n+1) xs
			   | otherwise = n:(getAvailableID (c-1) (n+1) (x:xs))
-}

getNewEdgeID :: DGraph -> Int
getNewEdgeID g = case getNewEdgeIDs 1 g of
		 [n] -> n
		 _ -> error "Static.DevGraph.getNewEdgeID"

getDGLinkLabWithIDs :: EdgeID -> DGraph -> Maybe DGLinkLab
getDGLinkLabWithIDs ids dgraph = 
   case getDGLEdgeWithIDs ids dgraph of
	Just (_, _, label) -> Just label
	Nothing -> Nothing
{-
   case [label|(_, _, label)<-labEdges dgraph, edge_id <- ids, 
	       elem edge_id $ dgl_id label] of
	[n] -> Just n
	_ -> Nothing 
-}

getDGLEdgeWithIDs :: EdgeID -> DGraph -> Maybe (LEdge DGLinkLab)
getDGLEdgeWithIDs ids dgraph = 
   case nub [ledge|ledge@(_, _, label)<-labEdges dgraph, edge_id <- ids, 
		   elem edge_id $ dgl_id label] of
	[n] -> Just n
	_ -> Nothing

getDGLEdgeWithIDsForSure :: EdgeID -> DGraph -> (LEdge DGLinkLab)
getDGLEdgeWithIDsForSure ids dgraph = 
   case getDGLEdgeWithIDs ids dgraph of
	Just e -> e
	Nothing -> error ("ID: "++show ids ++ 
			 "not found. Static.DevGraph.getDGLEdgeWithIDsForSure")
   {-
   case [ledge|ledge@(_, _, label)<-labEdges dgraph, edge_id <- ids, 
	       elem edge_id $ dgl_id label] of
	[n] -> n
	_ -> error (show ids ++ "Static.DevGraph.getDGLEdgeWithIDsForSure")
   -}

-- * Types for structured specification analysis

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???

-- | name of a node in a DG; auxiliary nodes may have extension string
--   and non-zero number (for these, names are usually hidden)
type NODE_NAME = (SIMPLE_ID, String, Int)

-- | node inscriptions in development graphs
data DGNodeLab =
  DGNode {
    dgn_name :: NODE_NAME,  -- name in the input language
    dgn_theory :: G_theory, -- local theory
    dgn_nf :: Maybe Node,   -- normal form, for Theorem-Hide-Shift
    dgn_sigma :: Maybe GMorphism, -- inclusion of signature into nf signature
    dgn_origin :: DGOrigin,  -- origin in input language
    dgn_cons :: Conservativity,
    dgn_cons_status :: ThmLinkStatus
  }
 | DGRef {  -- reference to node in a different DG
    dgn_name :: NODE_NAME,    -- new name of node (in current DG)
    dgn_libname :: LIB_NAME,     -- pointer to DG where ref'd node resides
    dgn_node :: Node,            -- pointer to ref'd node
    dgn_theory :: G_theory, -- local proof goals
    dgn_nf :: Maybe Node,        -- normal form, for Theorem-Hide-Shift
    dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  } deriving (Show, Eq)

dgn_sign :: DGNodeLab -> G_sign
dgn_sign dn = case dgn_theory dn of
    G_theory lid sig ind _ _-> G_sign lid sig ind

isInternalNode :: DGNodeLab -> Bool
isInternalNode (DGNode {dgn_name = n}) = isInternal n
isInternalNode (DGRef {dgn_name = n}) = null $ show $ getName n

isRefNode :: DGNodeLab -> Bool
isRefNode (DGNode {}) = False
isRefNode _ = True

-- | test for 'LeftOpen', return input for refs or no conservativity
hasOpenConsStatus :: Bool -> DGNodeLab -> Bool
hasOpenConsStatus b dgn = case dgn of
    DGRef {} -> b
    _ -> case dgn_cons dgn of
           None -> b
           _ -> case dgn_cons_status dgn of
                  LeftOpen -> True
                  _ -> False

-- | gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> String
getDGNodeType dgnodelab =
    (if hasOpenGoals dgnodelab then id else ("locallyEmpty__" ++))
    $ case isDGRef dgnodelab of
       True -> "dg_ref"
       False -> (if hasOpenConsStatus False dgnodelab
                 then "open_cons__"
                 else "proven_cons__")
                ++ if isInternalNode dgnodelab
                   then "internal"
                   else "spec"

-- gets the name of a development graph node as a string
getDGNodeName :: DGNodeLab -> String
getDGNodeName dgn = showName $ dgn_name dgn

emptyNodeName :: NODE_NAME
emptyNodeName = (mkSimpleId "", "", 0)

showInt :: Int -> String
showInt i = if i == 0 then "" else show i

showName :: NODE_NAME -> String
showName (n, s, i) = show n ++ if ext == "" then "" else "_" ++ ext
                   where ext = s ++ showInt i

makeName :: SIMPLE_ID -> NODE_NAME
makeName n = (n, "", 0)

getName :: NODE_NAME -> SIMPLE_ID
getName (n, _, _) = n

makeMaybeName :: Maybe SIMPLE_ID -> NODE_NAME
makeMaybeName Nothing = emptyNodeName
makeMaybeName (Just n) = makeName n

inc :: NODE_NAME -> NODE_NAME
inc (n, s, i) = (n, s, i+1)

isInternal :: NODE_NAME ->  Bool
isInternal (_, s, i) = i /= 0 || s /= ""

extName :: String -> NODE_NAME -> NODE_NAME
extName s (n, s1, i) = (n, s1 ++ showInt i ++ s, 0)

isDGRef :: DGNodeLab -> Bool
isDGRef (DGNode {}) = False
isDGRef (DGRef {}) = True

-- | test if a given node label has local open goals
hasOpenGoals ::  DGNodeLab -> Bool
hasOpenGoals dgn =
  case dgn_theory dgn of
  G_theory _lid _sigma _ sens _->
    not $ OMap.null $ OMap.filter
      (\s -> not (Logic.Prover.isAxiom s) && not (isProvenSenStatus s) ) sens

-- | link inscriptions in development graphs
data DGLinkLab = DGLink {
              dgl_morphism :: GMorphism,  -- signature morphism of link
              dgl_type :: DGLinkType,     -- type: local, global, def, thm?
              -- dgl_depends :: [Int],
              dgl_origin :: DGOrigin,  -- origin in input language
	      dgl_id :: EdgeID }   
              deriving (Show)

-- | to create a default ID which has to be changed by inserting of a certain edge.
defaultEdgeID :: EdgeID
defaultEdgeID = []

instance Eq DGLinkLab where
  l1 == l2 = (dgl_morphism l1 == dgl_morphism l2) 
	     && (dgl_type l1 == dgl_type l2) 
	     && (dgl_origin l1 == dgl_origin l2)

instance Pretty DGLinkLab where
  pretty l = fsep [ pretty (dgl_morphism l)
                  , pretty (dgl_type l)
                  , pretty (dgl_origin l)]

-- | coarser equality, ignoring the proof status
eqDGLinkLab :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLab l1 l2 = dgl_origin l1 == dgl_origin l2
  && dgl_morphism l1 == dgl_morphism l2
  && eqDGLinkType (dgl_type l1) (dgl_type l2)

eqLEdgeDGLinkLab :: LEdge DGLinkLab -> LEdge DGLinkLab -> Bool
eqLEdgeDGLinkLab (m1,n1,l1) (m2,n2,l2) =
   m1==m2 && n1==n2 && eqDGLinkLab l1 l2

--roughElem :: LEdge DGLinkLab -> [LEdge DGLinkLab] -> Bool
--roughElem x = any (`eqLEdgeDGLinkLab` x)
--roughElem (_, _, label) = any (\(_, _, l) -> dgl_id l == dgl_id label)
roughElem :: LEdge DGLinkLab -> [EdgeID] -> Bool
roughElem (_, _, label) = any (\edgeID -> not $ null $ intersect edgeID $ dgl_id label)


data DGChange = InsertNode (LNode DGNodeLab)
              | DeleteNode (LNode DGNodeLab)
              | InsertEdge (LEdge DGLinkLab)
              | DeleteEdge (LEdge DGLinkLab)
	      | SetNodeLab DGNodeLab (LNode DGNodeLab)
              deriving Eq

instance Show DGChange where
  show (InsertNode (n, _)) = "InsertNode "++show n -- ++show l
  show (DeleteNode (n, _)) = "DeleteNode "++show n -- ++show l
  show (InsertEdge (n,m, _)) = "InsertEdge "++show n++"->"++show m -- ++show l
  show (DeleteEdge (n,m, _)) = "DeleteEdge "++show n++"->"++show m -- ++show l
  show (SetNodeLab _ (n, _)) = "SetNodeLab of " ++ show n

-- | Link types of development graphs
--  Sect. IV:4.2 of the CASL Reference Manual explains them in depth
data DGLinkType = LocalDef
            | GlobalDef
            | HidingDef
            | FreeDef MaybeNode -- the "parameter" node
            | CofreeDef MaybeNode -- the "parameter" node
            | LocalThm ThmLinkStatus Conservativity ThmLinkStatus
               -- ??? Some more proof information is needed here
               -- (proof tree, ...)
            | GlobalThm ThmLinkStatus Conservativity ThmLinkStatus
            | HidingThm GMorphism ThmLinkStatus
            | FreeThm GMorphism ThmLinkStatus
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2
              deriving (Eq,Show)

thmLinkStatus :: DGLinkType -> Maybe ThmLinkStatus
thmLinkStatus (LocalThm s _ _) = Just s
thmLinkStatus (GlobalThm s _ _) = Just s
thmLinkStatus (HidingThm _ s) = Just s
thmLinkStatus (FreeThm _ s) = Just s
thmLinkStatus _ = Nothing

-- | Coarser equality ignoring the proof status
eqDGLinkType :: DGLinkType -> DGLinkType -> Bool
LocalDef `eqDGLinkType` LocalDef = True
HidingDef `eqDGLinkType` HidingDef = True
FreeDef n1 `eqDGLinkType` FreeDef n2 = n1==n2
LocalThm _ _ _ `eqDGLinkType`  LocalThm _ _ _ = True
GlobalThm _ _ _ `eqDGLinkType` GlobalThm _ _ _ = True
HidingThm m1 _ `eqDGLinkType` HidingThm m2 _ = m1 == m2
FreeThm m1 _ `eqDGLinkType` FreeThm m2 _ = m1 == m2
_ `eqDGLinkType` _ = False

instance Pretty DGLinkType where
    pretty t = text $ case t of
        LocalDef -> "LocalDef"
        GlobalDef -> "GlobalDef"
        HidingDef -> "HidingDef"
        FreeDef _ -> "FreeDef"
        CofreeDef _ -> "CofreeDef"
        LocalThm s _ _ -> "LocalThm" ++ getThmTypeAux s
        GlobalThm s _ _ -> "GlobalThm" ++ getThmTypeAux s
        HidingThm _ s -> "HidingThm" ++ getThmTypeAux s
        FreeThm _ s -> "FreeThm" ++ getThmTypeAux s

-- | describe the link type of the label
getDGLinkType :: DGLinkLab -> String
getDGLinkType lnk = let
    isHom = isHomogeneous $ dgl_morphism lnk
    het = if isHom then id else ("het" ++)
    in case dgl_morphism lnk of
 GMorphism _ _ _ _ _ ->
   case dgl_type lnk of
    GlobalDef -> if isHom then "globaldef"
          else "hetdef"
    HidingDef -> "hidingdef"
    LocalThm s _ _ -> het "local" ++ getThmType s ++ "thm"
    GlobalThm s _ _ -> het $ getThmType s ++ "thm"
    HidingThm _ s -> getThmType s ++ "hidingthm"
    FreeThm _ s -> getThmType s ++ "thm"
    _  -> "def" -- LocalDef, FreeDef, CofreeDef

-- | Conservativity annotations. For compactness, only the greatest
--   applicable value is used in a DG
data Conservativity = None | Cons | Mono | Def
              deriving (Eq,Ord)
instance Show Conservativity where
  show None = ""
  show Cons = "Cons"
  show Mono = "Mono"
  show Def = "Def"

-- | Rules in the development graph calculus,
--   Sect. IV:4.4 of the CASL Reference Manual explains them in depth
data DGRule =
   TheoremHideShift
 | HideTheoremShift (LEdge DGLinkLab)
 | Borrowing
 | ConsShift
 | DefShift
 | MonoShift
 | DefToMono
 | MonoToCons
 | FreeIsMono
 | MonoIsFree
 | GlobDecomp (LEdge DGLinkLab)  -- edge in the conclusion
 | LocDecomp (LEdge DGLinkLab)
 | LocInference (LEdge DGLinkLab)
 | GlobSubsumption (LEdge DGLinkLab)
 | Composition [LEdge DGLinkLab]
 | LocalInference
 | BasicInference AnyComorphism BasicProof -- coding and proof tree. obsolete?
 | BasicConsInference Edge BasicConsProof
   deriving (Show, Eq)

instance Pretty DGRule where
  pretty r = case r of
   TheoremHideShift -> text "Theorem-Hide-Shift"
   HideTheoremShift l -> text "Hide-Theorem-Shift; resulting link:"
                         <+> printLEdgeInProof l
   Borrowing -> text "Borrowing"
   ConsShift -> text "Cons-Shift"
   DefShift  -> text "Def-Shift"
   MonoShift -> text "Mono-Shift"
   DefToMono -> text "DefToMono"
   MonoToCons -> text "MonoToCons"
   FreeIsMono -> text "FreeIsMono"
   MonoIsFree -> text "MonoIsFree"
   GlobDecomp l -> text "Global Decomposition; resulting link:"
                   <+> printLEdgeInProof l
   LocDecomp l -> text "Local Decomposition; resulting link:"
                  <+> printLEdgeInProof l
   LocInference l -> text "Local Inference; resulting link:"
                     <+> printLEdgeInProof l
   GlobSubsumption l -> text "Global Subsumption; resulting link:"
                           <+> printLEdgeInProof l
   Composition ls ->
       text "Composition" <+> vcat (map printLEdgeInProof ls)
   LocalInference -> text "Local Inference"
   BasicInference c bp -> text "Basic Inference using:"
       <+> text ("Comorphism: "++show c ++ "Proof tree: "++show bp)
   BasicConsInference _ bp -> text "Basic Cons-Inference using:"
       <+> text (show bp)

printLEdgeInProof :: LEdge DGLinkLab -> Doc
printLEdgeInProof (s,t,l) =
  pretty s <> text "-->" <> pretty t <> text ":"
  <+> printLabInProof l

printLabInProof :: DGLinkLab -> Doc
printLabInProof l =
  fsep [ pretty (dgl_type l)
       , text "with origin:"
       , pretty (dgl_origin l) <> comma
       , text "and morphism:"
       , pretty (dgl_morphism l)
       ]

data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (Proof_status proof_tree)
     |  Guessed
     |  Conjectured
     |  Handwritten

instance Eq BasicProof where
  Guessed == Guessed = True
  Conjectured == Conjectured = True
  Handwritten == Handwritten = True
  BasicProof lid1 p1 == BasicProof lid2 p2 =
    coerceBasicProof lid1 lid2 "Eq BasicProof" p1 == Just p2
  _ == _ = False

instance Ord BasicProof where
    Guessed <= _ = True
    Conjectured <= x = case x of
                       Guessed -> False
                       _ ->  True
    Handwritten <= x = case x of
                       Guessed -> False
                       Conjectured -> False
                       _ ->  True
    BasicProof lid1 pst1 <= x =
        case x of
        BasicProof lid2 pst2
            | isProvedStat pst1 && not (isProvedStat pst2) -> False
            | not (isProvedStat pst1) && isProvedStat pst2 -> True
            | otherwise -> case primCoerce lid1 lid2 "" pst1 of
                           Nothing -> False
                           Just pst1' -> pst1' <= pst2
        _ -> False

instance Show BasicProof where
  show (BasicProof _ p1) = show p1
  show Guessed = "Guessed"
  show Conjectured = "Conjectured"
  show Handwritten = "Handwritten"

basicProofTc :: TyCon
basicProofTc = mkTyCon "Static.DevGraph.BasicProof"

instance Typeable BasicProof where
    typeOf _ = mkTyConApp basicProofTc []

data BasicConsProof = BasicConsProof -- more detail to be added ...
     deriving (Show, Eq)

type EdgeID = [Int] -- more to be added...

data ThmLinkStatus = LeftOpen
                   | Proven DGRule [EdgeID]
   --[LEdge DGLinkLab]  -- Proven DGRule Int
                     deriving (Show, Eq)

instance Pretty ThmLinkStatus where
    pretty tls = case tls of
        LeftOpen -> text "Open"
        Proven r ls -> fsep [ text "Proven with rule"
                            , pretty r
                            , text "Proof based on links:"
			    ] $+$ vcat(map printOneProofBasis ls)
                            --] $+$ vcat(map printLEdgeInProof ls)

printOneProofBasis :: EdgeID -> Doc
printOneProofBasis pb = pretty pb

-- | shows short theorem link status
getThmType :: ThmLinkStatus -> String
getThmType = map toLower . getThmTypeAux

getThmTypeAux :: ThmLinkStatus -> String
getThmTypeAux s = case s of
    LeftOpen -> "Unproven"
    _ -> "Proven"

{- | Data type indicating the origin of nodes and edges in the input language
     This is not used in the DG calculus, only may be used in the future
     for reconstruction of input and management of change. -}
data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree
              | DGLocal | DGClosed | DGClosedLenv | DGLogicQual
              | DGLogicQualLenv | DGData
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec
              | DGView SIMPLE_ID | DGFitView SIMPLE_ID | DGFitViewImp SIMPLE_ID
              | DGFitViewA SIMPLE_ID | DGFitViewAImp SIMPLE_ID | DGProof
              | DGintegratedSCC
              deriving (Show, Eq)

type DGraph = Tree.Gr DGNodeLab DGLinkLab
{- type DGraph = DGraph {  dgraph :: Tree.Gr DGNodeLab Int
                         , dgptr :: Int
                         , dglabels :: Map.Map Int (LEdge DGLinkLab) }
-}

-- | Node with signature in a DG
data NodeSig = NodeSig Node G_sign deriving (Show, Eq)

{- | NodeSig or possibly the empty sig in a logic
     (but since we want to avoid lots of vacuous nodes with empty sig,
     we do not assign a real node in the DG here) -}
data MaybeNode = JustNode NodeSig | EmptyNode AnyLogic deriving (Show, Eq)

instance Pretty NodeSig where
  pretty (NodeSig n sig) =
    text "node" <+> pretty n <> colon <> pretty sig

emptyG_sign :: AnyLogic -> G_sign
emptyG_sign (Logic lid) = G_sign lid (empty_signature lid) 0

getSig :: NodeSig -> G_sign
getSig (NodeSig _ sigma) = sigma

getNode :: NodeSig -> Node
getNode (NodeSig n _) = n

getMaybeSig :: MaybeNode -> G_sign
getMaybeSig (JustNode ns) = getSig ns
getMaybeSig (EmptyNode l) = emptyG_sign l

getLogic :: MaybeNode -> AnyLogic
getLogic (JustNode ns) = getNodeLogic ns
getLogic (EmptyNode l) = l

getNodeLogic :: NodeSig -> AnyLogic
getNodeLogic (NodeSig _ (G_sign lid _ _)) = Logic lid

-- | Create a node that represents a union of signatures
nodeSigUnion :: LogicGraph -> DGraph -> [MaybeNode] -> DGOrigin
             -> Result (NodeSig, DGraph)
nodeSigUnion lgraph dg nodeSigs orig =
  do sigUnion@(G_sign lid sigU ind) <- gsigManyUnion lgraph
                                   $ map getMaybeSig nodeSigs
     let nodeContents = DGNode {dgn_name = emptyNodeName,
                                dgn_theory = G_theory lid sigU ind noSens 0,
                                dgn_nf = Nothing,
                                dgn_sigma = Nothing,
                                dgn_origin = orig,
                                dgn_cons = None,
                                dgn_cons_status = LeftOpen}
         node = getNewNode dg
         dg' = insNode (node, nodeContents) dg
         inslink dgres nsig = do
             dgv <- dgres
             case nsig of
                 EmptyNode _ -> dgres
                 JustNode (NodeSig n sig) -> do
                     incl <- ginclusion lgraph sig sigUnion
                     return $ insEdge (n, node, DGLink
                         {dgl_morphism = incl,
                          dgl_type = GlobalDef,
                          dgl_origin = orig, 
			  dgl_id = [getNewEdgeID dgv]}) dgv
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig node sigUnion, dg'')

-- | Extend the development graph with given morphism originating
-- from given NodeSig
extendDGraph :: DGraph    -- ^ the development graph to be extended
             -> NodeSig   -- ^ the NodeSig from which the morphism originates
             -> GMorphism -- ^ the morphism to be inserted
             -> DGOrigin
             -> Result (NodeSig, DGraph)
-- ^ returns the target signature of the morphism and the resulting DGraph
extendDGraph dg (NodeSig n _) morph orig = case cod Grothendieck morph of
    targetSig@(G_sign lid tar ind) -> let
        nodeContents = DGNode {dgn_name = emptyNodeName,
                               dgn_theory = G_theory lid tar ind noSens 0,
                               dgn_nf = Nothing,
                               dgn_sigma = Nothing,
                               dgn_origin = orig,
                               dgn_cons = None,
                               dgn_cons_status = LeftOpen}
        linkContents = DGLink {dgl_morphism = morph,
                               dgl_type = GlobalDef, -- TODO: other type
                               dgl_origin = orig,
			       dgl_id = [getNewEdgeID dg']}
        node = getNewNode dg
        dg' = insNode (node, nodeContents) dg
        dg'' = insEdge (n, node, linkContents) dg'
        in return (NodeSig node targetSig, dg'')

-- | Extend the development graph with given morphism pointing to
-- given NodeSig
extendDGraphRev :: DGraph    -- ^ the development graph to be extended
             -> NodeSig   -- ^ the NodeSig to which the morphism points
             -> GMorphism -- ^ the morphism to be inserted
             -> DGOrigin
             -> Result (NodeSig, DGraph)
-- ^ returns the source signature of the morphism and the resulting DGraph
extendDGraphRev dg (NodeSig n _) morph orig = case dom Grothendieck morph of
    sourceSig@(G_sign lid src ind) -> let
        nodeContents = DGNode {dgn_name = emptyNodeName,
                               dgn_theory = G_theory lid src ind OMap.empty 0,
                               dgn_nf = Nothing,
                               dgn_sigma = Nothing,
                               dgn_origin = orig,
                               dgn_cons = None,
                               dgn_cons_status = LeftOpen}
        linkContents = DGLink {dgl_morphism = morph,
                               dgl_type = GlobalDef, -- TODO: other type
                               dgl_origin = orig,
			       dgl_id = [getNewEdgeID dg']}
        node = getNewNode dg
        dg' = insNode (node, nodeContents) dg
        dg'' = insEdge (node, n, linkContents) dg'
        in return (NodeSig node sourceSig, dg'')

-- import, formal parameters and united signature of formal params
type GenericitySig = (MaybeNode, [NodeSig], MaybeNode)

-- import, formal parameters, united signature of formal params, body
type ExtGenSig = (MaybeNode, [NodeSig], G_sign, NodeSig)

-- source, morphism, parameterized target
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)

-- * Types for architectural and unit specification analysis
-- (as defined for basic static semantics in Chap. III:5.1)

data UnitSig = Unit_sig NodeSig
             | Par_unit_sig [NodeSig] NodeSig
               deriving Show

data ImpUnitSigOrSig = Imp_unit_sig MaybeNode UnitSig
                     | Sig NodeSig
                       deriving Show

type StUnitCtx = Map.Map SIMPLE_ID ImpUnitSigOrSig
emptyStUnitCtx :: StUnitCtx
emptyStUnitCtx = Map.empty

data ArchSig = ArchSig StUnitCtx UnitSig deriving Show

-- * Types for global and library environments

data GlobalEntry = SpecEntry ExtGenSig
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig
                 | RefEntry
                   deriving Show

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

emptyHistory :: ([DGRule], [DGChange])
emptyHistory = ([], [])

type ProofHistory = [([DGRule], [DGChange])]
data GlobalContext = GlobalContext
    { globalAnnos :: GlobalAnnos
    , globalEnv :: GlobalEnv
    , devGraph :: DGraph
    , sigMap :: Map.Map Int G_sign
    , thMap :: Map.Map Int G_theory
    , morMap :: Map.Map Int G_morphism
    , proofHistory :: ProofHistory
    , redoHistory :: ProofHistory
    } deriving Show

emptyGlobalContext :: GlobalContext
emptyGlobalContext = GlobalContext
    { globalAnnos = emptyGlobalAnnos
    , globalEnv = Map.empty
    , devGraph = Graph.empty
    , sigMap = Map.empty
    , thMap = Map.empty
    , morMap = Map.empty
    , proofHistory = [emptyHistory]
    , redoHistory = []
    }

type LibEnv = Map.Map LIB_NAME GlobalContext

-- | an empty environment
emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

-- | returns the global context that belongs to the given library name
lookupGlobalContext :: LIB_NAME -> LibEnv -> GlobalContext
lookupGlobalContext ln =
    Map.findWithDefault (error "lookupGlobalContext") ln

-- | returns the development graph that belongs to the given library name
lookupDGraph :: LIB_NAME -> LibEnv -> DGraph
lookupDGraph ln = devGraph . lookupGlobalContext ln

instance Pretty DGOrigin where
  pretty origin = text $ case origin of
     DGBasic -> "basic specification"
     DGExtension -> "extension"
     DGTranslation -> "translation"
     DGUnion -> "union"
     DGHiding -> "hiding"
     DGRevealing -> "revealing"
     DGRevealTranslation -> "translation part of a revealing"
     DGFree -> "free specification"
     DGCofree -> "cofree specification"
     DGLocal -> "local specification"
     DGClosed -> "closed specification"
     DGClosedLenv -> "closed specification (inclusion of local environment)"
     DGFormalParams -> "formal parameters of a generic specification"
     DGImports -> "imports of a generic specification"
     DGSpecInst n -> "instantiation of " ++ tokStr n
     DGFitSpec -> "fittig specification"
     DGView n -> "view " ++ tokStr n
     DGFitView n -> "fitting view " ++ tokStr n
     DGFitViewImp n -> "fitting view (imports) " ++ tokStr n
     DGFitViewA n -> "fitting view (actual parameters) "++ tokStr n
     DGFitViewAImp n -> "fitting view (imports and actual parameters) "
                        ++ tokStr n
     DGProof -> "constructed within a proof"
     _ -> show origin

-- * Heterogenous sentences

type HetSenStatus a = SenStatus a (AnyComorphism,BasicProof)

isProvenSenStatus :: HetSenStatus a -> Bool
isProvenSenStatus = any isProvenSenStatusAux . thmStatus
  where isProvenSenStatusAux (_,BasicProof _ pst) = isProvedStat pst
        isProvenSenStatusAux _ = False
-- * Grothendieck theories

-- | Grothendieck theories
data G_theory = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_theory lid sign Int (ThSens sentence (AnyComorphism, BasicProof)) Int

coerceThSens ::
   (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m,
   Typeable b) => lid1 -> lid2 -> String
            -> ThSens sentence1 b -> m (ThSens sentence2 b)
coerceThSens l1 l2 msg t1 = primCoerce l1 l2 msg t1

instance Eq G_theory where
  G_theory l1 sig1 ind1 sens1 ind1'== G_theory l2 sig2 ind2 sens2 ind2'=
     G_sign l1 sig1 ind1 == G_sign l2 sig2 ind2
     && (ind1' > 0 && ind2' > 0 && ind1'==ind2'
         || coerceThSens l1 l2 "" sens1 == Just sens2)

instance Show G_theory where
  show (G_theory _ sign _ sens _) =
     show sign ++ "\n" ++ show sens

instance Pretty G_theory where
  pretty g = case simplifyTh g of
     G_theory lid sign _ sens _->
         pretty sign $++$ vsep (map (print_named lid)
                                           $ toNamedList sens)

-- | compute sublogic of a theory
sublogicOfTh :: G_theory -> G_sublogics
sublogicOfTh (G_theory lid sigma _ sens _) =
  let sub = foldl join
                  (minSublogic sigma)
                  (map snd $ OMap.toList $
                   OMap.map (minSublogic . value)
                       sens)
   in G_sublogics lid sub

-- | simplify a theory (throw away qualifications)
simplifyTh :: G_theory -> G_theory
simplifyTh (G_theory lid sigma ind1 sens ind2) = G_theory lid sigma ind1
      (OMap.map (mapValue $ simplify_sen lid sigma) sens) ind2

-- | apply a comorphism to a theory
mapG_theory :: AnyComorphism -> G_theory -> Result G_theory
mapG_theory (Comorphism cid) (G_theory lid sign ind1 sens ind2) = do
  bTh <- coerceBasicTheory lid (sourceLogic cid)
                    "mapG_theory" (sign, toNamedList sens)
  (sign', sens') <- wrapMapTheory cid bTh
  return $ G_theory (targetLogic cid) sign' ind1 (toThSens sens') ind2

-- | Translation of a G_theory along a GMorphism
translateG_theory :: GMorphism -> G_theory -> Result G_theory
translateG_theory (GMorphism cid _ _ morphism2 _)
                      (G_theory lid sign _ sens ind)  = do
  let tlid = targetLogic cid
  bTh <- coerceBasicTheory lid (sourceLogic cid)
                    "translateG_theory" (sign, toNamedList sens)
  (_, sens'') <- wrapMapTheory cid bTh
  sens''' <- mapM (mapNamedM $ map_sen tlid morphism2) sens''
  return $ G_theory tlid (cod tlid morphism2) 0 (toThSens sens''') ind

-- | Join the sentences of two G_theories
joinG_sentences :: Monad m => G_theory -> G_theory -> m G_theory
joinG_sentences (G_theory lid1 sig1 ind sens1 _)
                    (G_theory lid2 sig2 _ sens2 _) = do
  sens2' <- coerceThSens lid2 lid1 "joinG_sentences" sens2
  sig2' <- coerceSign lid2 lid1 "joinG_sentences" sig2
  return $ assert (sig1 == sig2')
             $ G_theory lid1 sig1 ind (joinSens sens2' sens1) 0


-- | flattening the sentences form a list of G_theories
flatG_sentences :: Monad m => G_theory -> [G_theory] -> m G_theory
flatG_sentences th ths = foldM joinG_sentences th ths

-- | Get signature of a theory
signOf :: G_theory -> G_sign
signOf (G_theory lid sign ind _ _) = G_sign lid sign ind

------------------------------------------------------------------
-- Grothendieck diagrams and weakly amalgamable cocones
------------------------------------------------------------------

type GDiagram = Tree.Gr G_theory GMorphism

gWeaklyAmalgamableCocone :: GDiagram
                         -> Result (G_theory, Map.Map Graph.Node GMorphism)
gWeaklyAmalgamableCocone _ =
    return (error "Static.DevGraph.gWeaklyAmalgamableCocone not yet implemented", Map.empty)
     -- dummy implementation
