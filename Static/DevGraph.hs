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
import Logic.Prover
import Static.GTheory

import Syntax.AS_Library

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.Graph.Inductive.Query.BFS as BFS
import qualified Common.Lib.Graph as Tree

import qualified Data.Map as Map
import qualified Common.OrderedMap as OMap

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result

import Control.Concurrent.MVar

import Data.Char (toLower)
import Data.List(find, intersect, partition)

getNewNode :: Tree.Gr a b -> Node
getNewNode g = case newNodes 1 g of
               [n] -> n
               _ -> error "Static.DevGraph.getNewNode"

getNewEdgeIDs :: Int -> DGraph -> [Int]
getNewEdgeIDs count g = take count [(getNewEdgeID g)..]

getDGLinkLabWithIDs :: EdgeID -> DGraph -> Maybe DGLinkLab
getDGLinkLabWithIDs ids dgraph =
   case getDGLEdgeWithIDs ids dgraph of
        Just (_, _, label) -> Just label
        Nothing -> Nothing

getDGLEdgeWithIDs :: EdgeID -> DGraph -> Maybe (LEdge DGLinkLab)
getDGLEdgeWithIDs ids dgraph =
   find (\ (_, _, label) -> isIdenticalEdgeID ids $ dgl_id label)
                                                 $ labEdges $ dgBody dgraph

isIdenticalEdgeID :: EdgeID -> EdgeID -> Bool
isIdenticalEdgeID id1 id2 = not $ null $ intersect id1 id2

getDGLEdgeWithIDsForSure :: EdgeID -> DGraph -> (LEdge DGLinkLab)
getDGLEdgeWithIDsForSure ids dgraph =
   case getDGLEdgeWithIDs ids dgraph of
        Just e -> e
        Nothing -> error ("ID: "++show ids ++
                         "not found. Static.DevGraph.getDGLEdgeWithIDsForSure")

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
  DGNode
  { dgn_name :: NODE_NAME        -- name in the input language
  , dgn_theory :: G_theory       -- local theory
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , dgn_origin :: DGOrigin       -- origin in input language
  , dgn_cons :: Conservativity
  , dgn_cons_status :: ThmLinkStatus
  , dgn_lock :: MVar ()
  }
 | DGRef -- reference to node in a different DG
  { dgn_name :: NODE_NAME        -- new name of node (in current DG)
  , dgn_libname :: LIB_NAME      -- pointer to DG where ref'd node resides
  , dgn_node :: Node             -- pointer to ref'd node
  , dgn_theory :: G_theory       -- local proof goals
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , dgn_lock :: MVar ()
  } deriving (Show, Eq)

instance Show (MVar ()) where
  show _ = ""

dgn_sign :: DGNodeLab -> G_sign
dgn_sign dn = case dgn_theory dn of
    G_theory lid sig ind _ _-> G_sign lid sig ind

isInternalNode :: DGNodeLab -> Bool
isInternalNode (DGNode {dgn_name = n}) = isInternal n
isInternalNode (DGRef {dgn_name = n}) = null $ show $ getName n

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
      (\s -> not (isAxiom s) && not (isProvenSenStatus s) ) sens

-- | link inscriptions in development graphs
data DGLinkLab = DGLink {
              dgl_morphism :: GMorphism,  -- signature morphism of link
              dgl_type :: DGLinkType,     -- type: local, global, def, thm?
              -- dgl_depends :: [Int],
              dgl_origin :: DGOrigin,  -- origin in input language
              dgl_id :: EdgeID }
              deriving (Show)

-- | create a default ID which has to be changed when inserting a certain edge.
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

roughElem :: LEdge DGLinkLab -> [EdgeID] -> Bool
roughElem (_, _, label) =
    any (\edgeID -> isIdenticalEdgeID  edgeID $ dgl_id label)


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
     let nodeContents = DGNode { dgn_name = emptyNodeName
                               , dgn_theory = G_theory lid sigU ind noSens 0
                               , dgn_nf = Nothing
                               , dgn_sigma = Nothing
                               , dgn_origin = orig
                               , dgn_cons = None
                               , dgn_cons_status = LeftOpen
                               , dgn_lock = error "MVar not initialized"
                               }
         node = getNewNodeDG dg
         --dg' = insNode (node, nodeContents) graphBody
         dg' = insNodeDG (node, nodeContents) dg
         inslink dgres nsig = do
             dgv <- dgres
             case nsig of
                 EmptyNode _ -> dgres
                 JustNode (NodeSig n sig) -> do
                     incl <- ginclusion lgraph sig sigUnion
                     return $ insEdgeDG (n, node, DGLink
                         { dgl_morphism = incl
                         , dgl_type = GlobalDef
                         , dgl_origin = orig
                         , dgl_id = [getNewEdgeID dgv]
                         }) dgv
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
        nodeContents = DGNode { dgn_name = emptyNodeName
                              , dgn_theory = G_theory lid tar ind noSens 0
                              , dgn_nf = Nothing
                              , dgn_sigma = Nothing
                              , dgn_origin = orig
                              , dgn_cons = None
                              , dgn_cons_status = LeftOpen
                              , dgn_lock = error "MVar not initialized"
                              }
        linkContents = DGLink { dgl_morphism = morph
                              , dgl_type = GlobalDef
                              , dgl_origin = orig
                              , dgl_id = [getNewEdgeID dg']
                              }
        node = getNewNodeDG dg
        dg' = insNodeDG (node, nodeContents) dg
        dg'' = insEdgeDG (n, node, linkContents) dg'
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
        nodeContents = DGNode { dgn_name = emptyNodeName
                              , dgn_theory = G_theory lid src ind OMap.empty 0
                              , dgn_nf = Nothing
                              , dgn_sigma = Nothing
                              , dgn_origin = orig
                              , dgn_cons = None
                              , dgn_cons_status = LeftOpen
                              , dgn_lock = error "uninitialized MVar of DGNode"
                              }
        linkContents = DGLink { dgl_morphism = morph
                              , dgl_type = GlobalDef
                              , dgl_origin = orig
                              , dgl_id = [getNewEdgeID dg']
                              }
        node = getNewNodeDG dg
        dg' = insNodeDG (node, nodeContents) dg
        dg'' = insEdgeDG (node, n, linkContents) dg'
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
    , getNewEdgeID :: Int  -- ^ edge counter
    , refNodes :: Map.Map Node (LIB_NAME, Node) -- ^ unexpanded 'DGRef's
    , allRefNodes :: Map.Map (LIB_NAME, Node) Node -- ^ all DGRef's
    , sigMap :: Map.Map Int G_sign -- ^ signature map
    , thMap :: Map.Map Int G_theory -- ^ morphism map
    , morMap :: Map.Map Int G_morphism -- ^ theory map
    , proofHistory :: ProofHistory -- ^ applied proof steps
    , redoHistory :: ProofHistory -- ^ undone proofs steps
    , openlock :: MVar () -- ^ control of graph display
    , localproof :: MVar () -- ^ control of graph proof
    }

setSigMapDG :: Map.Map Int G_sign -> DGraph -> DGraph
setSigMapDG m dg = dg{sigMap = m}

setThMapDG :: Map.Map Int G_theory -> DGraph -> DGraph
setThMapDG m dg = dg{thMap = m}

setMorMapDG :: Map.Map Int G_morphism -> DGraph -> DGraph
setMorMapDG m dg = dg{morMap = m}

lookupSigMapDG :: Int -> DGraph -> Maybe G_sign
lookupSigMapDG i = Map.lookup i . sigMap

lookupThMapDG :: Int -> DGraph -> Maybe G_theory
lookupThMapDG i = Map.lookup i . thMap

lookupMorMapDG :: Int -> DGraph -> Maybe G_morphism
lookupMorMapDG i = Map.lookup i . morMap

lookupGlobalEnvDG :: SIMPLE_ID -> DGraph -> Maybe GlobalEntry
lookupGlobalEnvDG sid = Map.lookup sid . globalEnv

emptyDG :: DGraph
emptyDG = DGraph
    { globalAnnos = emptyGlobalAnnos
    , globalEnv = Map.empty
    , dgBody = Graph.empty
    , getNewEdgeID = 0
    , refNodes = Map.empty
    , allRefNodes = Map.empty
    , sigMap = Map.empty
    , thMap = Map.empty
    , morMap = Map.empty
    , proofHistory = [emptyHistory]
    , redoHistory = [emptyHistory]
    , openlock = error "uninitialized MVar of DGraph"
    , localproof = error "uninitialized MVar of DGraph"
    }

emptyDGwithMVar :: IO DGraph
emptyDGwithMVar = do
  ol <- newEmptyMVar
  lp <- newEmptyMVar
  return $ emptyDG {openlock = ol, localproof = lp}

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

-- | returns the global context that belongs to the given library name
lookupDGraph :: LIB_NAME -> LibEnv -> DGraph
lookupDGraph ln =
    Map.findWithDefault (error "lookupDGraph") ln

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
     DGFitViewA n -> "fitting view (actual parameters) " ++ tokStr n
     DGFitViewAImp n ->
         "fitting view (imports and actual parameters) " ++ tokStr n
     DGProof -> "constructed within a proof"
     _ -> show origin

-- | Heterogenous sentences
type HetSenStatus a = SenStatus a (AnyComorphism,BasicProof)

isProvenSenStatus :: HetSenStatus a -> Bool
isProvenSenStatus = any isProvenSenStatusAux . thmStatus
  where isProvenSenStatusAux (_,BasicProof _ pst) = isProvedStat pst
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

-- | Grothendieck diagrams
type GDiagram = Tree.Gr G_theory GMorphism

-- | weakly amalgamable cocones
gWeaklyAmalgamableCocone
    :: GDiagram -> Result (G_theory, Map.Map Graph.Node GMorphism)
gWeaklyAmalgamableCocone _ = return
    ( error "Static.DevGraph.gWeaklyAmalgamableCocone not yet implemented"
    , Map.empty) -- dummy implementation

-- | get the available node id
getNewNodeDG :: DGraph -> Node
getNewNodeDG = getNewNode . dgBody

delNodeDG :: Node -> DGraph -> DGraph
delNodeDG n dg =
  dg{dgBody = delNode n $ dgBody dg}

delLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
delLNodeDG n@(v, l) g = case matchDG v g of
    (Just(p, _, l', s), g') ->
       if l' == l then
           if null p && null s then g'
           else error $ "delLNodeDG remaining edges: " ++ show (p ++ s)
       else error $ "delLNodeDG wrong label: " ++ show n
    _ -> error $ "delLNodeDG no such node: " ++ show n

delNodesDG :: [Node] -> DGraph -> DGraph
delNodesDG ns dg =
  dg{dgBody = delNodes ns $ dgBody dg}

-- | insert a new node into given DGraph
insNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insNodeDG n dg =
  dg{dgBody = insNode n $ dgBody dg}

addToRefNodesDG :: (Node, LIB_NAME, Node) -> DGraph -> DGraph
addToRefNodesDG (n, libn, refn) dg =
       dg{refNodes = Map.insert n (libn, refn) $ refNodes dg,
          allRefNodes = Map.insert (libn, refn) n $ allRefNodes dg}

deleteFromRefNodesDG :: Node -> DGraph -> DGraph
deleteFromRefNodesDG n dg = dg{refNodes = Map.delete n $ refNodes dg}

lookupInRefNodesDG :: Node -> DGraph -> Maybe (LIB_NAME, Node)
lookupInRefNodesDG n dg =
    Map.lookup n $ refNodes dg

lookupInAllRefNodesDG :: (LIB_NAME, Node) -> DGraph -> Maybe Node
lookupInAllRefNodesDG refK dg =
    Map.lookup refK $ allRefNodes dg

insLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insLNodeDG n@(v, _) g =
    if gelemDG v g then error $ "insLNodeDG " ++ show v else insNodeDG n g

-- | insert a new node with the given node content into a given DGraph
insNodesDG :: [LNode DGNodeLab] -> DGraph -> DGraph
insNodesDG ns dg =
  dg{dgBody = insNodes ns $ dgBody dg}

delEdgeDG :: Edge -> DGraph -> DGraph
delEdgeDG e dg =
  dg {dgBody = delEdge e $ dgBody dg}

delEdgesDG :: [Edge] -> DGraph -> DGraph
delEdgesDG es dg =
  dg {dgBody = delEdges es $ dgBody dg}

delLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdgeDG e@(v, w, l) g = case matchDG v g of
    (Just(p, v', l', s), g') ->
        let (ls, rs) = partition ((l, w) ==) s in
        case ls of
          [] -> error $ "delLEdgeDG no edge: " ++ show e
          [_] -> g'{dgBody = (p, v', l', rs) & (dgBody g')}
          _ -> error $ "delLEdgeDG multiple edges: " ++ show e
    _ -> error $ "delLEdgeDG no node for edge: " ++ show e

insLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeDG e@(v, w, l) g = case matchDG v g of
    (Just(p, v', l', s), g') ->
        let ls = filter ((l, w) ==) s in
        case ls of
          [] -> g'{getNewEdgeID = getNewEdgeID g' + 1,
                   dgBody = (p, v', l', (l, w) : s) & (dgBody g')}
          _ -> error $ "insLEdgeDG multiple edge: " ++ show e
    _ -> error $ "insLEdgeDG no node for edge: " ++ show e

insLEdgeNubDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeNubDG (v, w, l) g =
   if (l, w) `elem` s then g
      else g'{getNewEdgeID = getNewEdgeID g'+1,
              dgBody =
             (p, v, l', (l{dgl_id=[getNewEdgeID g]}, w) : s) & (dgBody g')}
   where (Just (p, _, l', s), g') = matchDG v g

-- | insert an edge into the given DGraph, which updates
-- the graph body and the edge counter as well.
insEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
insEdgeDG l oldDG =
  oldDG { dgBody = insEdge l $ dgBody oldDG
        , getNewEdgeID = getNewEdgeID oldDG + 1 }

insEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
insEdgesDG = flip $ foldr insEdgeDG

-- | get all the edges
labEdgesDG :: DGraph -> [LEdge DGLinkLab]
labEdgesDG = labEdges . dgBody

-- | get all the nodes
labNodesDG :: DGraph -> [LNode DGNodeLab]
labNodesDG = labNodes . dgBody

contextDG :: DGraph -> Node -> Context DGNodeLab DGLinkLab
contextDG = context . dgBody

mkGraphDG :: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> DGraph -> DGraph
mkGraphDG ns ls dg = insEdgesDG ls $ insNodesDG ns dg

matchDG :: Node -> DGraph -> (MContext DGNodeLab DGLinkLab, DGraph)
matchDG n dg =
  let
  (mc, newBody) = match n $ dgBody dg
  in
  (mc, dg{dgBody = newBody})

sccDG :: DGraph -> [[Node]]
sccDG = DFS.scc . dgBody

topsortDG :: DGraph -> [Node]
topsortDG = DFS.topsort . dgBody

isEmptyDG :: DGraph -> Bool
isEmptyDG = isEmpty . dgBody

gelemDG :: Node -> DGraph -> Bool
gelemDG n = (gelem n) . dgBody

noNodesDG :: DGraph -> Int
noNodesDG = noNodes . dgBody

preDG :: DGraph -> Node -> [Node]
preDG = pre . dgBody

innDG :: DGraph -> Node -> [LEdge DGLinkLab]
innDG = inn . dgBody

outDG :: DGraph -> Node -> [LEdge DGLinkLab]
outDG = out . dgBody

nodesDG :: DGraph -> [Node]
nodesDG = nodes . dgBody

edgesDG :: DGraph -> [Edge]
edgesDG = edges . dgBody

labDG :: DGraph -> Node -> Maybe DGNodeLab
labDG = lab . dgBody

newNodesDG :: Int -> DGraph -> [Node]
newNodesDG n = newNodes n . dgBody

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

labelNodeDG :: LNode DGNodeLab -> DGraph -> (DGraph, DGNodeLab)
labelNodeDG (v, l) g = case matchDG v g of
    (Just(p, _, o, s), g') -> (g'{dgBody = (p, v, l, s) & (dgBody g')}, o)
    _ -> error $ "labelNodeDG no such node: " ++ show v

setProofHistoryDG :: ProofHistory -> DGraph -> DGraph
setProofHistoryDG h c = c{proofHistory = proofHistory c ++ h}

addToProofHistoryDG :: ([DGRule], [DGChange]) -> DGraph -> DGraph
addToProofHistoryDG x dg = dg{proofHistory = x:proofHistory dg}

setProofHistoryWithDG :: (ProofHistory -> ProofHistory)
                      -> DGraph -> DGraph
setProofHistoryWithDG f dg = dg{proofHistory = f $ proofHistory dg}
