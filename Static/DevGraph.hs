{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Central datastructures for development graphs
   Follows Sect. IV:4.2 of the CASL Reference Manual.

We also provide functions for constructing and modifying development graphs.
However note that these changes need to be propagated to the GUI if they
also shall be visible in the displayed development graph.
See 'Proofs.EdgeUtils.updateWithChanges'
and 'Proofs.StatusUtils.mkResultProofStatus'.
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
import Logic.Comorphism(mkIdComorphism)
import Common.ExtSign
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Prover
import Static.GTheory

import Syntax.AS_Library

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.Graph.Inductive.Query.BFS as BFS
import qualified Common.Lib.Graph as Tree

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.OrderedMap as OMap

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result

import Control.Concurrent.MVar
import Control.Exception (assert)

import Data.Char (toLower)
import Data.List (partition)

import Static.WACocone
import Common.SFKT

{- | returns one new node id for the given graph
-}
getNewNode :: Tree.Gr a b -> Node
getNewNode g = case newNodes 1 g of
               [n] -> n
               _ -> error "Static.DevGraph.getNewNode"

-- * Types for structured specification analysis

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???

-- | name of a node in a DG; auxiliary nodes may have extension string
--   and non-zero number (for these, names are usually hidden)
type NODE_NAME = (SIMPLE_ID, String, Int)

data DGNodeInfo = DGNode
  { node_origin :: DGOrigin       -- origin in input language
  , node_cons :: Conservativity
  , node_cons_status :: ThmLinkStatus }
  | DGRef                        -- reference to node in a different DG
  { ref_libname :: LIB_NAME      -- pointer to DG where ref'd node resides
  , ref_node :: Node             -- pointer to ref'd node
  } deriving (Show, Eq)

dgn_origin :: DGNodeLab -> DGOrigin
dgn_origin = node_origin . nodeInfo

dgn_cons :: DGNodeLab -> Conservativity
dgn_cons = node_cons . nodeInfo

dgn_cons_status :: DGNodeLab -> ThmLinkStatus
dgn_cons_status = node_cons_status . nodeInfo

dgn_libname :: DGNodeLab -> LIB_NAME
dgn_libname = ref_libname . nodeInfo

dgn_node :: DGNodeLab -> Node
dgn_node = ref_node . nodeInfo

-- | node inscriptions in development graphs
data DGNodeLab =
  DGNodeLab
  { dgn_name :: NODE_NAME        -- name in the input language
  , dgn_theory :: G_theory       -- local theory
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , nodeInfo :: DGNodeInfo
  , dgn_lock :: Maybe (MVar ())
  } deriving (Show, Eq)

instance Show (MVar ()) where
  show _ = ""

showLNode :: LNode DGNodeLab -> String
showLNode (n, l) = "node " ++ show n ++ ": " ++ getDGNodeType l

dgn_sign :: DGNodeLab -> G_sign
dgn_sign dn = case dgn_theory dn of
    G_theory lid sig ind _ _-> G_sign lid sig ind

isInternalNode :: DGNodeLab -> Bool
isInternalNode l@DGNodeLab {dgn_name = n} =
    if isDGRef l then null $ show $ getName n else isInternal n

-- | test for 'LeftOpen', return input for refs or no conservativity
hasOpenConsStatus :: Bool -> DGNodeLab -> Bool
hasOpenConsStatus b dgn = if isDGRef dgn then b else
    case dgn_cons dgn of
           None -> b
           _ -> case dgn_cons_status dgn of
                  LeftOpen -> True
                  _ -> False

-- | gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> String
getDGNodeType dgnodelab =
    (if hasOpenGoals dgnodelab then id else ("locallyEmpty__" ++))
    $ if isDGRef dgnodelab then "dg_ref" else
      (if hasOpenConsStatus False dgnodelab
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
isDGRef l = case nodeInfo l of
    DGNode {} -> False
    DGRef {} -> True

-- | test if a given node label has local open goals
hasOpenGoals ::  DGNodeLab -> Bool
hasOpenGoals dgn =
  case dgn_theory dgn of
  G_theory _lid _sigma _ sens _->
    not $ OMap.null $ OMap.filter
      (\s -> not (isAxiom s) && not (isProvenSenStatus s) ) sens

{- | an edge id is represented as a list of ints.
     the reason of an edge can have multiple ids is, for example, there exists
     an proven edge e1 with id 1 and an unproven edge e2 with id 2 between
     two nodes. Now after applying some rules e2 is proven, but it's actually
     the same as the proven edge e1, then the proven e2 should not be inserted
     into the graph again, but e1 will take e2's id 2 because 2 is probably
     saved in some other places. As a result, e1 would have 1 and 2 as its id.
     This type can be extended to a more complicated struture, like a tree
     suggested by Till.
-}

newtype EdgeId = EdgeId Int deriving (Eq, Ord, Enum, Show)

instance Pretty EdgeId where
   pretty (EdgeId i) = pretty i

-- | create a default ID which has to be changed when inserting a certain edge.
defaultEdgeId :: EdgeId
defaultEdgeId = EdgeId (-1)

startEdgeId :: EdgeId
startEdgeId = EdgeId 0

incEdgeId :: EdgeId -> EdgeId
incEdgeId (EdgeId i) = EdgeId (i + 1)

newtype ProofBasis = ProofBasis { proofBasis :: Set.Set EdgeId }
    deriving (Eq, Ord, Show)

emptyProofBasis :: ProofBasis
emptyProofBasis = ProofBasis Set.empty

nullProofBasis :: ProofBasis -> Bool
nullProofBasis = Set.null . proofBasis

addEdgeId :: ProofBasis -> EdgeId -> ProofBasis
addEdgeId (ProofBasis s) e = ProofBasis $ Set.insert e s

{- | checks if the given edge is contained in the given proof basis..
-}
roughElem :: LEdge DGLinkLab -> ProofBasis -> Bool
roughElem (_, _, label) = Set.member (dgl_id label) . proofBasis

-- | link inscriptions in development graphs
data DGLinkLab = DGLink
    { dgl_morphism :: GMorphism  -- signature morphism of link
    , dgl_type :: DGLinkType     -- type: local, global, def, thm?
    , dgl_origin :: DGOrigin     -- origin in input language
    , dgl_id :: !EdgeId          -- id of the edge
    } deriving (Show, Eq)

showLEdge :: LEdge DGLinkLab -> String
showLEdge (source, target, l) =
  show (dgl_id l) ++ ": " ++ show source ++ "->" ++ show target
           ++ " from " ++ show (dgl_origin l)
           ++ " with type " ++ getDGLinkType l

-- | equality without comparing the edge ids
eqDGLinkLabContent :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLabContent l1 l2 = let
    i1 = dgl_id l1
    i2 = dgl_id l2
  in if i1 <= defaultEdgeId || i2 <= defaultEdgeId then
    dgl_morphism l1 == dgl_morphism l2
  && dgl_type l1 == dgl_type l2
  && dgl_origin l1 == dgl_origin l2
  else let r = eqDGLinkLabContent l1 l2 { dgl_id = defaultEdgeId}
           s = i1 == i2
       in assert (r == s) s

eqDGLinkLabById :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLabById l1 l2 = let
    i1 = dgl_id l1
    i2 = dgl_id l2
    in if i1 > defaultEdgeId && i2 > defaultEdgeId then i1 == i2 else
       error "eqDGLinkLabById"

instance Pretty DGLinkLab where
  pretty l = vcat
    [ text $ show $ dgl_id l
    , text "Origin:"
    , pretty $ dgl_origin l
    , text "Type:"
    , pretty $ dgl_type l
    , text "Morphism:"
    , pretty $ dgl_morphism l ]

{- | the edit operations of the DGraph
-}
data DGChange =
    InsertNode (LNode DGNodeLab)
  | DeleteNode (LNode DGNodeLab)
  | InsertEdge (LEdge DGLinkLab)
  | DeleteEdge (LEdge DGLinkLab)
  -- it contains the old label and new label with node
  | SetNodeLab DGNodeLab (LNode DGNodeLab)
  deriving Eq

instance Show DGChange where
  show = showDGChange

showDGChange :: DGChange -> String
showDGChange c = case c of
  DeleteEdge e -> "delete " ++ showLEdge e
  InsertEdge e -> "insert " ++ showLEdge e
  InsertNode n -> "insert " ++ showLNode n
  DeleteNode n -> "delete " ++ showLNode n
  SetNodeLab l n -> "change '" ++ getDGNodeType l ++ "' to " ++ showLNode n

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
              deriving (Show, Eq)

thmLinkStatus :: DGLinkType -> Maybe ThmLinkStatus
thmLinkStatus (LocalThm s _ _) = Just s
thmLinkStatus (GlobalThm s _ _) = Just s
thmLinkStatus (HidingThm _ s) = Just s
thmLinkStatus (FreeThm _ s) = Just s
thmLinkStatus _ = Nothing

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
 GMorphism cid _ _ _ _ ->
   case dgl_type lnk of
    GlobalDef -> if isHom then "globaldef" ++ inc'
          else "hetdef" ++ inc'
    HidingDef -> "hidingdef" ++ inc'
    LocalThm s _ _ -> het "local" ++ getThmType s ++ "thm" ++ inc'
    GlobalThm s _ _ -> het $ getThmType s ++ "thm" ++ inc'
    HidingThm _ s -> getThmType s ++ "hidingthm" ++ inc'
    FreeThm _ s -> getThmType s ++ "thm" ++ inc'
    LocalDef -> "localdef" ++ inc'
    _  -> "def" ++ inc' -- FreeDef, CofreeDef
  where
    inc' = if isInclComorphism $ Comorphism cid then "Inc" else ""

-- | Conservativity annotations. For compactness, only the greatest
--   applicable value is used in a DG
data Conservativity = None | Cons | Mono | Def deriving (Eq, Ord)

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
 | ComputeColimit
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
   ComputeColimit -> text"ComputeColimit"
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

data BasicConsProof = BasicConsProof -- more detail to be added ...
     deriving (Show, Eq)

data ThmLinkStatus = LeftOpen
                   | Proven DGRule ProofBasis
                     deriving (Show, Eq)

isProvenThmLinkStatus :: ThmLinkStatus -> Bool
isProvenThmLinkStatus tls = case tls of
  LeftOpen -> False
  _ -> True

instance Pretty ThmLinkStatus where
    pretty tls = case tls of
        LeftOpen -> text "Open"
        Proven r ls -> fsep [ text "Proven with rule"
                            , pretty r
                            , text "Proof based on links:"
                            , pretty $ Set.toList $ proofBasis ls
                            ]

-- | shows short theorem link status
getThmType :: ThmLinkStatus -> String
getThmType = map toLower . getThmTypeAux

getThmTypeAux :: ThmLinkStatus -> String
getThmTypeAux s = if isProvenThmLinkStatus s then "Proven" else "Unproven"

{- | Data type indicating the origin of nodes and edges in the input language
     This is not used in the DG calculus, only may be used in the future
     for reconstruction of input and management of change. -}
data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree
              | DGLocal | DGClosed | DGClosedLenv | DGLogicQual
              | DGData
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec
              | DGView SIMPLE_ID | DGFitView SIMPLE_ID | DGFitViewImp SIMPLE_ID
              | DGFitViewA SIMPLE_ID | DGFitViewAImp SIMPLE_ID | DGProof
              | DGintegratedSCC | DGEmpty
              deriving Eq

instance Show DGOrigin where
  show o = case o of
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
     DGLogicQual -> "specification with logic qualifier"
     DGFormalParams -> "formal parameters of a generic specification"
     DGImports -> "imports of a generic specification"
     DGSpecInst n -> "instantiation of " ++ tokStr n
     DGFitSpec -> "fittig specification"
     DGView n -> "view " ++ tokStr n
     DGFitView n -> "fitting view " ++ tokStr n
     DGFitViewImp n -> "fitting view (imports) " ++ tokStr n
     DGFitViewA n -> "fitting view (actual parameters) " ++ tokStr n
     DGFitViewAImp n ->
         "fitting view (imports and actual parameters) " ++ tokStr n
     DGProof -> "proof construct"
     DGEmpty -> "empty specification"
     DGData -> "data specification"
     DGintegratedSCC ->
         "OWL spec with integrated strongly connected components"

instance Pretty DGOrigin where
  pretty = text . show

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
emptyG_sign (Logic lid) = G_sign lid (ext_empty_signature lid) 0

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

newNodeInfo :: DGOrigin -> DGNodeInfo
newNodeInfo orig = DGNode
  { node_origin = orig
  , node_cons = None
  , node_cons_status = LeftOpen }

newRefInfo :: LIB_NAME -> Node -> DGNodeInfo
newRefInfo ln n = DGRef
  { ref_libname = ln
  , ref_node = n }

newInfoNodeLab :: NODE_NAME -> DGNodeInfo -> G_theory -> DGNodeLab
newInfoNodeLab name info gTh = DGNodeLab
  { dgn_name = name
  , dgn_theory = gTh
  , dgn_nf = Nothing
  , dgn_sigma = Nothing
  , nodeInfo = info
  , dgn_lock = Nothing }

-- | create a new node label
newNodeLab :: NODE_NAME -> DGOrigin -> G_theory -> DGNodeLab
newNodeLab name orig = newInfoNodeLab name (newNodeInfo orig)

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

data GlobalEntry =
    SpecEntry ExtGenSig
  | ViewEntry ExtViewSig
  | ArchEntry ArchSig
  | UnitEntry UnitSig
  | RefEntry
    deriving Show

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

emptyHistory :: ([DGRule], [DGChange])
emptyHistory = ([], [])

type ProofHistory = [([DGRule], [DGChange])]

{- | the actual development graph with auxiliary information. A
  'G_sign' should be stored in 'sigMap' under its 'gSignSelfIdx'. The
  same applies to 'G_morphism' with 'morMap' and 'gMorphismSelfIdx'
  resp. 'G_theory' with 'thMap' and 'gTheorySelfIdx'. -}
data DGraph = DGraph
    { globalAnnos :: GlobalAnnos -- ^ global annos of library
    , globalEnv :: GlobalEnv -- ^ name entities (specs, views) of a library
    , dgBody :: Tree.Gr DGNodeLab DGLinkLab  -- ^ actual 'DGraph` tree
    , getNewEdgeId :: !EdgeId  -- ^ edge counter
    , refNodes :: Map.Map Node (LIB_NAME, Node) -- ^ unexpanded 'DGRef's
    , allRefNodes :: Map.Map (LIB_NAME, Node) Node -- ^ all DGRef's
    , sigMap :: Map.Map Int G_sign -- ^ signature map
    , thMap :: Map.Map Int G_theory -- ^ morphism map
    , morMap :: Map.Map Int G_morphism -- ^ theory map
    , proofHistory :: ProofHistory -- ^ applied proof steps
    , redoHistory :: ProofHistory -- ^ undone proofs steps
    , openlock :: Maybe (MVar (IO ())) -- ^ control of graph display
    }

emptyDG :: DGraph
emptyDG = DGraph
    { globalAnnos = emptyGlobalAnnos
    , globalEnv = Map.empty
    , dgBody = Graph.empty
    , getNewEdgeId = startEdgeId
    , refNodes = Map.empty
    , allRefNodes = Map.empty
    , sigMap = Map.empty
    , thMap = Map.empty
    , morMap = Map.empty
    , proofHistory = [emptyHistory]
    , redoHistory = [emptyHistory]
    , openlock = Nothing
    }

emptyDGwithMVar :: IO DGraph
emptyDGwithMVar = do
  ol <- newEmptyMVar
  return $ emptyDG {openlock = Just ol}

-----------------------
-- some set functions
-----------------------
setSigMapDG :: Map.Map Int G_sign -> DGraph -> DGraph
setSigMapDG m dg = dg{sigMap = m}

setThMapDG :: Map.Map Int G_theory -> DGraph -> DGraph
setThMapDG m dg = dg{thMap = m}

setMorMapDG :: Map.Map Int G_morphism -> DGraph -> DGraph
setMorMapDG m dg = dg{morMap = m}

-----------------------
-- some lookup functions
-----------------------

lookupSigMapDG :: Int -> DGraph -> Maybe G_sign
lookupSigMapDG i = Map.lookup i . sigMap

lookupThMapDG :: Int -> DGraph -> Maybe G_theory
lookupThMapDG i = Map.lookup i . thMap

lookupMorMapDG :: Int -> DGraph -> Maybe G_morphism
lookupMorMapDG i = Map.lookup i . morMap

lookupGlobalEnvDG :: SIMPLE_ID -> DGraph -> Maybe GlobalEntry
lookupGlobalEnvDG sid = Map.lookup sid . globalEnv

getMapAndMaxIndex :: (b -> Map.Map Int a) -> b -> (Map.Map Int a, Int)
getMapAndMaxIndex f gctx =
    let m = f gctx in (m, if Map.null m then 0 else fst $ Map.findMax m)

sigMapI :: DGraph -> (Map.Map Int G_sign, Int)
sigMapI = getMapAndMaxIndex sigMap

morMapI :: DGraph -> (Map.Map Int G_morphism, Int)
morMapI = getMapAndMaxIndex morMap

thMapI :: DGraph -> (Map.Map Int G_theory, Int)
thMapI = getMapAndMaxIndex thMap

type LibEnv = Map.Map LIB_NAME DGraph

-- | an empty environment
emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

-- | returns the DGraph that belongs to the given library name
lookupDGraph :: LIB_NAME -> LibEnv -> DGraph
lookupDGraph ln =
    Map.findWithDefault (error "lookupDGraph") ln

-- | Heterogenous sentences
type HetSenStatus a = SenStatus a (AnyComorphism,BasicProof)

isProvenSenStatus :: HetSenStatus a -> Bool
isProvenSenStatus = any isProvenSenStatusAux . thmStatus
  where isProvenSenStatusAux (_, BasicProof _ pst) = isProvedStat pst
        isProvenSenStatusAux _ = False

-- * Grothendieck theory with prover

-- | a pair of prover and theory which are in the same logic
data G_theory_with_prover =
    forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_theory_with_prover lid
                       (Theory sign sentence proof_tree)
                       (Prover sign sentence sublogics proof_tree)

-- | weakly amalgamable cocones
gWeaklyAmalgamableCocone :: GDiagram -> Result (G_theory, Map.Map Int GMorphism)
gWeaklyAmalgamableCocone diag =
 if isHomogeneousGDiagram diag then do
  case head $ labNodes diag of
   (_, G_theory lid _ _ _ _) -> do
    graph <- homogeniseGDiagram lid diag
    (sig, mor) <- signature_colimit lid graph
                  -- until the amalgamability check is fixed
    let gth = G_theory lid (mkExtSign sig) 0 noSens 0
        cid = mkIdComorphism lid (top_sublogic lid)
        morFun = Map.fromList $
         map (\(n, s)->(n, GMorphism cid (mkExtSign s) 0 (mor Map.! n) 0)) $
         labNodes graph
    return (gth, morFun)
 else if not $ isConnected diag then fail "Graph is not connected"
      else if not $ isAcyclic $ removeIdentities diag then
             -- TO DO: instead of acyclic, test whether the diagram is thin
           fail "Graph is not acyclic" else do
             let funDesc = initDescList diag
             graph <- observe $ hetWeakAmalgCocone diag funDesc
               -- TO DO: modify this function so it would return
               -- all possible answers and offer them as choices to the user
             buildStrMorphisms diag graph

-- | get the available node id
getNewNodeDG :: DGraph -> Node
getNewNodeDG = getNewNode . dgBody

-- | delete the node out of the given DG
delNodeDG :: Node -> DGraph -> DGraph
delNodeDG n dg =
  dg{dgBody = delNode n $ dgBody dg}

-- | delete the LNode out of the given DG
delLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
delLNodeDG n@(v, l) g = case matchDG v g of
    (Just(p, _, l', s), g') ->
      if l' == l then
          if null p && null s then g'
          else error $ "delLNodeDG remaining edges: " ++ show (p ++ s)
      else error $ "delLNodeDG wrong label: " ++ show n
    _ -> error $ "delLNodeDG no such node: " ++ show n

-- | delete a list of nodes out of the given DG
delNodesDG :: [Node] -> DGraph -> DGraph
delNodesDG ns dg =
  dg{dgBody = delNodes ns $ dgBody dg}

-- | insert a new node into given DGraph
insNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insNodeDG n dg =
  dg{dgBody = insNode n $ dgBody dg}

-- | add a new referenced node into the refNodes map of the given DG
addToRefNodesDG :: (Node, LIB_NAME, Node) -> DGraph -> DGraph
addToRefNodesDG (n, libn, refn) dg =
       dg{refNodes = Map.insert n (libn, refn) $ refNodes dg,
          allRefNodes = Map.insert (libn, refn) n $ allRefNodes dg}

-- | delete the given referenced node out of the refnodes map
deleteFromRefNodesDG :: Node -> DGraph -> DGraph
deleteFromRefNodesDG n dg = dg{refNodes = Map.delete n $ refNodes dg}

-- | lookup a referenced node with a node id
lookupInRefNodesDG :: Node -> DGraph -> Maybe (LIB_NAME, Node)
lookupInRefNodesDG n dg =
    Map.lookup n $ refNodes dg

-- | look up a refernced node with its parent infor.
lookupInAllRefNodesDG :: (LIB_NAME, Node) -> DGraph -> Maybe Node
lookupInAllRefNodesDG refK dg =
    Map.lookup refK $ allRefNodes dg

-- | inserts a lnode into a given DG
insLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insLNodeDG n@(v, _) g =
    if gelemDG v g then error $ "insLNodeDG " ++ show v else insNodeDG n g

-- | insert a new node with the given node content into a given DGraph
insNodesDG :: [LNode DGNodeLab] -> DGraph -> DGraph
insNodesDG ns dg =
  dg{dgBody = insNodes ns $ dgBody dg}

-- | delete an edge out of a given DG
delEdgeDG :: Edge -> DGraph -> DGraph
delEdgeDG e dg =
  dg {dgBody = delEdge e $ dgBody dg}

-- | delete a list of edges
delEdgesDG :: [Edge] -> DGraph -> DGraph
delEdgesDG es dg =
  dg {dgBody = delEdges es $ dgBody dg}

-- | delete a labeled edge out of the given DG
delLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdgeDG e@(v, w, l) g = case matchDG v g of
    (Just(p, v', l', s), g') ->
        let (ls, rs) = partition (\ (sl, sw) ->
              sw == w && eqDGLinkLabById sl l) s in
        case ls of
          [] -> error $ "delLEdgeDG no edge: " ++ showLEdge e
          _ -> g'{dgBody = (p, v', l', rs) & (dgBody g')}
          -- _ -> error $ "delLEdgeDG multiple edges: " ++ showLEdge e
    _ -> error $ "delLEdgeDG no node for edge: " ++ showLEdge e

-- | insert a labeled edge into a given DG
insLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeDG e@(v, w, l) g = if dgl_id l == defaultEdgeId then
    error "insLEdgeDG" else case matchDG v g of
    (Just(p, v', l', s), g') ->
        let ls = filter (\ (l2, w2) -> w == w2
               && eqDGLinkLabContent l { dgl_id = defaultEdgeId } l2) s in
        case ls of
          [] -> g'{getNewEdgeId = incEdgeId $ getNewEdgeId g',
                   dgBody = (p, v', l', (l, w) : s) & (dgBody g')}
          _ -> error $ "insLEdgeDG multiple edge: " ++ showLEdge e
    _ -> error $ "insLEdgeDG no node for edge: " ++ showLEdge e

{- | tries to insert a labeled edge into a given DG, but if this edge
     already exists, then does nothing
-}
insLEdgeNubDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeNubDG (v, w, l) g =
   if any (\ (l2, w2) -> w == w2 && eqDGLinkLabContent l l2) s then g
      else g'{getNewEdgeId = incEdgeId oldEdgeId,
              dgBody =
             (p, v, l', (l{dgl_id = oldEdgeId }, w)
                   : s) & dgBody g'}
   where (Just (p, _, l', s), g') = matchDG v g
         oldEdgeId = getNewEdgeId g'

-- | insert an edge into the given DGraph, which updates
-- the graph body and the edge counter as well.
insEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
insEdgeDG l oldDG =
  oldDG { dgBody = insEdge l $ dgBody oldDG
        , getNewEdgeId = incEdgeId $ getNewEdgeId oldDG }

-- | insert a list of labeled edge into a given DG
insEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
insEdgesDG = flip $ foldr insEdgeDG

-- | get all the edges
labEdgesDG :: DGraph -> [LEdge DGLinkLab]
labEdgesDG = labEdges . dgBody

-- | get all the nodes
labNodesDG :: DGraph -> [LNode DGNodeLab]
labNodesDG = labNodes . dgBody

-- | get the context of the given DG
contextDG :: DGraph -> Node -> Context DGNodeLab DGLinkLab
contextDG = context . dgBody

-- | merge a list of lnodes and ledges into a given DG
mkGraphDG :: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> DGraph -> DGraph
mkGraphDG ns ls dg = insEdgesDG ls $ insNodesDG ns dg

-- | tear the given DGraph appart.
matchDG :: Node -> DGraph -> (MContext DGNodeLab DGLinkLab, DGraph)
matchDG n dg =
  let
  (mc, newBody) = match n $ dgBody dg
  in
  (mc, dg{dgBody = newBody})

-- | get all nodes of a given DG with scc algorithm
sccDG :: DGraph -> [[Node]]
sccDG = DFS.scc . dgBody

-- | get the list of nodes in top sorted order
topsortDG :: DGraph -> [Node]
topsortDG = DFS.topsort . dgBody

-- | checks if a DG is empty or not.
isEmptyDG :: DGraph -> Bool
isEmptyDG = isEmpty . dgBody

-- | checks if a given node belongs to a given DG
gelemDG :: Node -> DGraph -> Bool
gelemDG n = (gelem n) . dgBody

-- | get the number of nodes of a given DG
noNodesDG :: DGraph -> Int
noNodesDG = noNodes . dgBody

-- | get all nodes which links to the given node in a given DG
preDG :: DGraph -> Node -> [Node]
preDG = pre . dgBody

-- | get all the incoming ledges of the given node in a given DG
innDG :: DGraph -> Node -> [LEdge DGLinkLab]
innDG = inn . dgBody

-- | get all the outgoing ledges of the given node in a given DG
outDG :: DGraph -> Node -> [LEdge DGLinkLab]
outDG = out . dgBody

-- | get all the nodes of the given DG
nodesDG :: DGraph -> [Node]
nodesDG = nodes . dgBody

-- | get all the edges of the given DG
edgesDG :: DGraph -> [Edge]
edgesDG = edges . dgBody

-- | tries to get the label of the given node in a given DG
labDG :: DGraph -> Node -> DGNodeLab
labDG dg = maybe (error "labDG") id . lab (dgBody dg)

-- | gets the given number of new node-ids in a given DG.
newNodesDG :: Int -> DGraph -> [Node]
newNodesDG n = newNodes n . dgBody

-- | gets all nodes in a breadth-first sorted order.
bfsDG :: Node -> DGraph -> [Node]
bfsDG n = BFS.bfs n . dgBody

-- | safe context for graphs
safeContext :: (Show a, Show b, Graph gr) => String -> gr a b -> Node
            -> Context a b
safeContext err g v =
  case match v g of
    (Nothing,_) -> error (err++": Match Exception, Node: "++show v++
                          " not present in graph with nodes:\n"++
                          show (nodes g)++"\nand edges:\n"++show (edges g))
    (Just c,_)  -> c

-- | make it not so general ;)
safeContextDG :: String -> DGraph -> Node -> Context DGNodeLab DGLinkLab
safeContextDG s dg n = safeContext s (dgBody dg) n

-- | sets the node with new label and returns the new graph and the old label
labelNodeDG :: LNode DGNodeLab -> DGraph -> (DGraph, DGNodeLab)
labelNodeDG (v, l) g = case matchDG v g of
    (Just(p, _, o, s), g') -> (g'{dgBody = (p, v, l, s) & (dgBody g')}, o)
    _ -> error $ "labelNodeDG no such node: " ++ show v

-- | add a proof history into current one of the given DG
setProofHistoryDG :: ProofHistory -> DGraph -> DGraph
setProofHistoryDG h dg = dg { proofHistory = proofHistory dg ++ h }
-- is appending at the end correct?

-- | add a history item into current history.
addToProofHistoryDG :: ([DGRule], [DGChange]) -> DGraph -> DGraph
addToProofHistoryDG x dg = dg { proofHistory = x : proofHistory dg }

-- | update the proof history with a function
setProofHistoryWithDG :: (ProofHistory -> ProofHistory)
                      -> DGraph -> DGraph
setProofHistoryWithDG f dg = dg{proofHistory = f $ proofHistory dg}

{- | Acquire the local lock. If already locked it waits till it is unlocked
     again.-}
lockLocal :: DGNodeLab -> IO ()
lockLocal dgn = case dgn_lock dgn of
  Just lock -> putMVar lock ()
  Nothing -> error "MVar not initialised"

-- | Tries to acquire the local lock. Return False if already acquired.
tryLockLocal :: DGNodeLab -> IO Bool
tryLockLocal dgn =  case dgn_lock dgn of
  Just lock -> tryPutMVar lock ()
  Nothing -> error "MVar not initialised"


-- | Releases the local lock.
unlockLocal :: DGNodeLab -> IO ()
unlockLocal dgn = case dgn_lock dgn of
  Just lock -> do
    unlocked <- tryTakeMVar lock
    case unlocked of
      Just () -> return ()
      Nothing -> error "Local lock wasn't locked."
  Nothing -> error "MVar not initialised"

-- | initializes the MVar for locking if nessesary
initLocking :: DGraph -> LNode DGNodeLab -> IO (DGraph, DGNodeLab)
initLocking dg (node, dgn) = do
  lock <- newEmptyMVar
  let dgn' = dgn{dgn_lock = Just lock}
  return (fst $ labelNodeDG (node, dgn') dg, dgn')

-- | checks if locking MVar is initialized
hasLock :: DGNodeLab -> Bool
hasLock dgn = case dgn_lock dgn of
  Just _ -> True
  Nothing -> False
