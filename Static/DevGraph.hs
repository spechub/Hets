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

import Static.GTheory
import Syntax.AS_Library (LIB_NAME)
import Syntax.Print_AS_Library ()

import Logic.Logic
import Logic.ExtSign
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Prover

import qualified Common.Lib.Graph as Tree
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id

import Control.Concurrent.MVar
import Control.Exception (assert)

import Data.Char (toLower)
import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set


import Comorphisms.LogicGraph
import Common.Result

-- * types for structured specification analysis

-- ** basic types

-- | Node with signature in a DG
data NodeSig = NodeSig Node G_sign deriving (Show, Eq)

{- | NodeSig or possibly the empty sig in a logic
     (but since we want to avoid lots of vacuous nodes with empty sig,
     we do not assign a real node in the DG here) -}
data MaybeNode = JustNode NodeSig | EmptyNode AnyLogic deriving (Show, Eq)

-- | Conservativity annotations. For compactness, only the greatest
--   applicable value is used in a DG
data Conservativity = None | Cons | Mono | Def deriving (Show, Eq, Ord)

data BasicConsProof = BasicConsProof deriving (Show, Eq) -- needs more details

-- ** node label types

-- | name of a node in a DG; auxiliary nodes may have extension string
--   and non-zero number (for these, names are usually hidden)
data NodeName = NodeName SIMPLE_ID String Int deriving (Show, Eq, Ord)

isInternal :: NodeName ->  Bool
isInternal (NodeName _ s i) = i /= 0 || s /= ""

getName :: NodeName -> SIMPLE_ID
getName (NodeName n _ _) = n

{- | Data type indicating the origin of nodes and edges in the input language
     This is not used in the DG calculus, only may be used in the future
     for reconstruction of input and management of change. -}
data DGOrigin =
    DGEmpty
  | DGBasic
  | DGExtension
  | DGTranslation
  | DGUnion
  | DGHiding
  | DGRevealing
  | DGRevealTranslation
  | DGFree
  | DGCofree
  | DGLocal
  | DGClosed
  | DGLogicQual
  | DGData
  | DGFormalParams
  | DGImports
  | DGSpecInst SIMPLE_ID
  | DGFitSpec
  | DGFitView SIMPLE_ID
  | DGFitViewA SIMPLE_ID
  | DGProof
  | DGintegratedSCC
    deriving (Show, Eq)

-- | node content or reference to another library's node
data DGNodeInfo = DGNode
  { node_origin :: DGOrigin       -- origin in input language
  , node_cons_status :: Maybe Bool } -- unused currently
  | DGRef                        -- reference to node in a different DG
  { ref_libname :: LIB_NAME      -- pointer to DG where ref'd node resides
  , ref_node :: Node             -- pointer to ref'd node
  } deriving (Show, Eq)

-- | test for 'LeftOpen', return input for refs or no conservativity
getConsState :: Bool -> DGNodeInfo -> Bool
getConsState b c = case c of
  DGRef {} -> b
  DGNode {} -> case node_cons_status c of
    Nothing -> b
    Just s -> not s

-- | show cons status as string
showConsState :: DGNodeInfo -> String
showConsState l =
  (if getConsState False l then "open" else "proven") ++ "_cons"

-- | node inscriptions in development graphs
data DGNodeLab =
  DGNodeLab
  { dgn_name :: NodeName        -- name in the input language
  , dgn_theory :: G_theory       -- local theory
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , nodeInfo :: DGNodeInfo
  , dgn_lock :: Maybe (MVar ())
  } deriving (Show, Eq)

instance Show (MVar a) where
  show _ = ""

isDGRef :: DGNodeLab -> Bool
isDGRef l = case nodeInfo l of
    DGNode {} -> False
    DGRef {} -> True

-- | test a theory sentence
isProvenSenStatus :: SenStatus a (AnyComorphism, BasicProof) -> Bool
isProvenSenStatus = any isProvenSenStatusAux . thmStatus
  where isProvenSenStatusAux (_, BasicProof _ pst) = isProvedStat pst
        isProvenSenStatusAux _ = False

-- | test if a given node label has local open goals
hasOpenGoals ::  DGNodeLab -> Bool
hasOpenGoals dgn = case dgn_theory dgn of
  G_theory _lid _sigma _ sens _-> not $ OMap.null $ OMap.filter
      (\ s -> not (isAxiom s) && not (isProvenSenStatus s)) sens

-- | check if the node has an internal name (wrong for DGRef?)
isInternalNode :: DGNodeLab -> Bool
isInternalNode l@DGNodeLab {dgn_name = n} =
    if isDGRef l then null $ show $ getName n else isInternal n

hasOpenConsStatus :: Bool -> DGNodeLab -> Bool
hasOpenConsStatus b = getConsState b . nodeInfo

-- | gets the type of a development graph edge as a string
getDGNodeType :: DGNodeLab -> String
getDGNodeType dgnodelab =
    (if hasOpenGoals dgnodelab then id else ("locallyEmpty__" ++))
    $ if isDGRef dgnodelab then "dg_ref" else
      showConsState (nodeInfo dgnodelab) ++ "__"
      ++ if isInternalNode dgnodelab
         then "internal"
         else "spec"

data DGNodeType = NotEmptyOpenConsSpec
                | NotEmptyProvenConsSpec
                | LocallyEmptyOpenConsSpec
                | LocallyEmptyProvenConsSpec
                | NotEmptyOpenConsInternal
                | NotEmptyProvenConsInternal
                | LocallyEmptyOpenConsInternal
                | LocallyEmptyProvenConsInternal
                | NotEmptyDGRef
                | LocallyEmptyDGRef
                  deriving (Show, Eq, Ord)

-- | gets the type of a development graph edge as a datatype
getRealDGNodeType :: DGNodeLab -> DGNodeType
getRealDGNodeType dgnodelab = case (loc,ref,con,int) of
  (True, True,_,_) -> NotEmptyDGRef
  (False,True,_,_) -> LocallyEmptyDGRef
  (True, _,True, True ) -> NotEmptyOpenConsInternal
  (True, _,True, False) -> NotEmptyOpenConsSpec
  (True, _,False,True ) -> NotEmptyProvenConsInternal
  (True, _,False,False) -> NotEmptyProvenConsSpec
  (False,_,True, True ) -> LocallyEmptyOpenConsInternal
  (False,_,True, False) -> LocallyEmptyOpenConsSpec
  (False,_,False,True ) -> LocallyEmptyProvenConsInternal
  (False,_,False,False) -> LocallyEmptyProvenConsSpec
  where
    loc = hasOpenGoals dgnodelab
    ref = isDGRef dgnodelab
    con = getConsState False (nodeInfo dgnodelab)
    int = isInternalNode dgnodelab

-- ** edge label types

{- an edge id used to be represented as a list of ints.
     the reason of an edge can have multiple ids is, for example, there exists
     an proven edge e1 with id 1 and an unproven edge e2 with id 2 between
     two nodes. Now after applying some rules e2 is proven, but it's actually
     the same as the proven edge e1, then the proven e2 should not be inserted
     into the graph again, but e1 will take e2's id 2 because 2 is probably
     saved in some other places. As a result, e1 would have 1 and 2 as its id.
     This type can be extended to a more complicated struture, like a tree
     suggested by Till.
-}

-- | unique number for edges
newtype EdgeId = EdgeId Int deriving (Show, Eq, Ord, Enum)

-- | the first edge in a graph
startEdgeId :: EdgeId
startEdgeId = EdgeId 0

-- | a set of used edges
newtype ProofBasis = ProofBasis { proofBasis :: Set.Set EdgeId }
    deriving (Show, Eq, Ord)

data DGLinkOrigin =
    SeeTarget
  | SeeSource
  | DGLinkExtension
  | DGLinkTranslation
  | DGLinkClosedLenv
  | DGLinkImports
  | DGLinkSpecInst SIMPLE_ID
  | DGLinkFitSpec
  | DGLinkView SIMPLE_ID
  | DGLinkFitView SIMPLE_ID
  | DGLinkFitViewImp SIMPLE_ID
  | DGLinkFitViewAImp SIMPLE_ID
  | DGLinkProof
    deriving (Show, Eq)

{- | Rules in the development graph calculus,
   Sect. IV:4.4 of the CASL Reference Manual explains them in depth
   mutual recursive with 'DGLinkLab', 'DGLinkType', and 'ThmLinkStatus'
-}
data DGRule =
    TheoremHideShift
  | HideTheoremShift (LEdge DGLinkLab)
  | ComputeColimit
  | NormalForm
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
  | BasicInference AnyComorphism BasicProof -- coding and proof tree. obsolete?
  | BasicConsInference Edge BasicConsProof
  | Flattening                            -- from level 1 to level 0
    deriving (Show, Eq)

-- | proof status of a link
data ThmLinkStatus = LeftOpen | Proven DGRule ProofBasis deriving (Show, Eq)

isProvenThmLinkStatus :: ThmLinkStatus -> Bool
isProvenThmLinkStatus tls = case tls of
  LeftOpen -> False
  _ -> True

-- | show theorem link status
getThmTypeAux :: ThmLinkStatus -> String
getThmTypeAux s = if isProvenThmLinkStatus s then "Proven" else "Unproven"

-- | show theorem link status (using lower case letter)
getThmType :: ThmLinkStatus -> String
getThmType = map toLower . getThmTypeAux

-- | Link types of development graphs
--  Sect. IV:4.2 of the CASL Reference Manual explains them in depth
data DGLinkType =
    LocalDef
  | GlobalDef
  | HidingDef
  | FreeDef MaybeNode -- the "parameter" node
  | CofreeDef MaybeNode -- the "parameter" node
  | LocalThm ThmLinkStatus Conservativity ThmLinkStatus
    -- ??? Some more proof information is needed here (proof tree, ...)
  | GlobalThm ThmLinkStatus Conservativity ThmLinkStatus
  | HidingThm GMorphism ThmLinkStatus
  | FreeThm GMorphism ThmLinkStatus
    -- DGLink S1 S2 m2 (DGLinkType m1 p) n
    -- corresponds to a span of morphisms
    -- S1 <--m1-- S --m2--> S2
    deriving (Show, Eq)

-- | extract theorem link status from link type
thmLinkStatus :: DGLinkType -> Maybe ThmLinkStatus
thmLinkStatus t = case t of
    LocalThm s _ _ -> Just s
    GlobalThm s _ _ -> Just s
    HidingThm _ s -> Just s
    FreeThm _ s -> Just s
    _ -> Nothing

-- | link inscriptions in development graphs
data DGLinkLab = DGLink
  { dgl_morphism :: GMorphism  -- signature morphism of link
  , dgl_type :: DGLinkType     -- type: local, global, def, thm?
  , dgl_origin :: DGLinkOrigin -- origin in input language
  , dgl_id :: EdgeId          -- id of the edge
  } deriving (Show, Eq)

-- | describe the link type of the label
getDGLinkType :: DGLinkLab -> String
getDGLinkType lnk = let
    isHom = isHomogeneous $ dgl_morphism lnk
    het = if isHom then id else ("het" ++)
    inc' = case dgl_morphism lnk of
             GMorphism cid _ _ mor _ ->
               if isInclusionComorphism cid && isInclusion mor
               then (++ "Inc") else id
    thmType = maybe "" getThmType $ thmLinkStatus $ dgl_type lnk
    in inc' $ case dgl_type lnk of
    GlobalDef -> if isHom then "globaldef" else "hetdef"
    HidingDef -> "hidingdef"
    LocalThm _ _ _ -> het "local" ++ thmType ++ "thm"
    GlobalThm _ _ _ -> het thmType ++ "thm"
    HidingThm _ _ -> thmType ++ "hidingthm"
    FreeThm _ _ -> thmType ++ "thm"
    LocalDef -> "localdef"
    _  -> "def" -- FreeDef, CofreeDef

data DGEdgeType = GlobalDefNoInc
                | GlobalDefInc
                | LocalDefNoInc
                | LocalDefInc
                | DefNoInc
                | DefInc
                | HidingDefNoInc
                | HidingDefInc
                | HetDefNoInc
                | HetDefInc
                | ProvenThmNoInc
                | ProvenThmInc
                | UnprovenThmNoInc
                | UnprovenThmInc
                | LocalProvenThmNoInc
                | LocalProvenThmInc
                | LocalUnprovenThmNoInc
                | LocalUnprovenThmInc
                | HetProvenThmNoInc
                | HetProvenThmInc
                | HetUnprovenThmNoInc
                | HetUnprovenThmInc
                | HetLocalProvenThmNoInc
                | HetLocalProvenThmInc
                | HetLocalUnprovenThmNoInc
                | HetLocalUnprovenThmInc
                | UnprovenHidingThmNoInc
                | UnprovenHidingThmInc
                | ProvenHidingThmNoInc
                | ProvenHidingThmInc
                | ReferenceNoInc
                | ReferenceInc
                  deriving (Show, Eq, Ord)

-- | describe the link type of the label
getRealDGLinkType :: DGLinkLab -> DGEdgeType
getRealDGLinkType lnk = case (dgl,hom,thm,inc') of
  (GlobalDef,True ,_,True ) -> GlobalDefInc
  (GlobalDef,True ,_,False) -> GlobalDefNoInc
  (GlobalDef,False,_,True ) -> HetDefInc
  (GlobalDef,False,_,False) -> HetDefNoInc
  (HidingDef,_,_,True ) -> HidingDefInc
  (HidingDef,_,_,False) -> HidingDefNoInc
  (LocalThm _ _ _,True, True, True ) -> LocalProvenThmInc
  (LocalThm _ _ _,True, True, False) -> LocalProvenThmNoInc
  (LocalThm _ _ _,True, False,True ) -> LocalUnprovenThmInc
  (LocalThm _ _ _,True, False,False) -> LocalUnprovenThmNoInc
  (LocalThm _ _ _,False,True, True ) -> HetLocalProvenThmInc
  (LocalThm _ _ _,False,True, False) -> HetLocalProvenThmNoInc
  (LocalThm _ _ _,False,False,True ) -> HetLocalUnprovenThmInc
  (LocalThm _ _ _,False,False,False) -> HetLocalUnprovenThmNoInc
  (GlobalThm _ _ _,True, True, True ) -> ProvenThmInc
  (GlobalThm _ _ _,True, True, False) -> ProvenThmNoInc
  (GlobalThm _ _ _,True, False,True ) -> UnprovenThmInc
  (GlobalThm _ _ _,True, False,False) -> UnprovenThmNoInc
  (GlobalThm _ _ _,False,True, True ) -> HetProvenThmInc
  (GlobalThm _ _ _,False,True, False) -> HetProvenThmNoInc
  (GlobalThm _ _ _,False,False,True ) -> HetUnprovenThmInc
  (GlobalThm _ _ _,False,False,False) -> HetUnprovenThmNoInc
  (HidingThm _ _,_,True, True ) -> ProvenHidingThmInc
  (HidingThm _ _,_,True, False) -> ProvenHidingThmNoInc
  (HidingThm _ _,_,False,True ) -> UnprovenHidingThmInc
  (HidingThm _ _,_,False,False) -> UnprovenHidingThmNoInc
  (FreeThm _ _,_,True, True ) -> ProvenThmInc
  (FreeThm _ _,_,True, False) -> ProvenThmNoInc
  (FreeThm _ _,_,False,True ) -> UnprovenThmInc
  (FreeThm _ _,_,False,False) -> UnprovenThmNoInc
  (LocalDef,_,_,True ) -> LocalDefInc
  (LocalDef,_,_,False) -> LocalDefNoInc
  (_,_,_,True ) -> DefInc
  (_,_,_,False) -> DefNoInc
  where
    hom = isHomogeneous $ dgl_morphism lnk
    dgl = dgl_type lnk
    inc' = case dgl_morphism lnk of
            GMorphism cid _ _ mor _ ->
              isInclusionComorphism cid && isInclusion mor
    thm = maybe (error "getRealDGLinkType error") (isProvenThmLinkStatus)
                $ thmLinkStatus $ dgl_type lnk

-- ** types for global environments

-- | import, formal parameters and united signature of formal params
data GenericitySig = GenericitySig MaybeNode [NodeSig] MaybeNode deriving Show

-- | import, formal parameters, united signature of formal params, body
data ExtGenSig = ExtGenSig MaybeNode [NodeSig] G_sign NodeSig deriving Show

-- | source, morphism, parameterized target
data ExtViewSig = ExtViewSig NodeSig GMorphism ExtGenSig deriving Show

{- ** types for architectural and unit specification analysis
    (as defined for basic static semantics in Chap. III:5.1) -}

data UnitSig = UnitSig NodeSig | ParUnitSig [NodeSig] NodeSig deriving Show

data ImpUnitSigOrSig = ImpUnitSig MaybeNode UnitSig | Sig NodeSig deriving Show

type StUnitCtx = Map.Map SIMPLE_ID ImpUnitSigOrSig

emptyStUnitCtx :: StUnitCtx
emptyStUnitCtx = Map.empty

data ArchSig = ArchSig StUnitCtx UnitSig deriving Show

-- | an entry of the global environment
data GlobalEntry =
    SpecEntry ExtGenSig
  | ViewEntry ExtViewSig
  | ArchEntry ArchSig
  | UnitEntry UnitSig
  | RefEntry
    deriving Show

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

-- ** change and history types

-- | the edit operations of the DGraph
data DGChange =
    InsertNode (LNode DGNodeLab)
  | DeleteNode (LNode DGNodeLab)
  | InsertEdge (LEdge DGLinkLab)
  | DeleteEdge (LEdge DGLinkLab)
  -- it contains the old label and new label with node
  | SetNodeLab DGNodeLab (LNode DGNodeLab)
  deriving (Show, Eq)

type ProofHistory = [([DGRule], [DGChange])]

emptyHistory :: ([DGRule], [DGChange])
emptyHistory = ([], [])

{- | the actual development graph with auxiliary information. A
  'G_sign' should be stored in 'sigMap' under its 'gSignSelfIdx'. The
  same applies to 'G_morphism' with 'morMap' and 'gMorphismSelfIdx'
  resp. 'G_theory' with 'thMap' and 'gTheorySelfIdx'. -}
data DGraph = DGraph
  { globalAnnos :: GlobalAnnos -- ^ global annos of library
  , globalEnv :: GlobalEnv -- ^ name entities (specs, views) of a library
  , dgBody :: Tree.Gr DGNodeLab DGLinkLab  -- ^ actual 'DGraph` tree
  , getNewEdgeId :: EdgeId  -- ^ edge counter
  , refNodes :: Map.Map Node (LIB_NAME, Node) -- ^ unexpanded 'DGRef's
  , allRefNodes :: Map.Map (LIB_NAME, Node) Node -- ^ all DGRef's
  , sigMap :: Map.Map SigId G_sign -- ^ signature map
  , thMap :: Map.Map ThId G_theory -- ^ morphism map
  , morMap :: Map.Map MorId G_morphism -- ^ theory map
  , proofHistory :: ProofHistory -- ^ applied proof steps
  , redoHistory :: ProofHistory -- ^ undone proofs steps
  , openlock :: Maybe (MVar (ProofHistory -> IO ()))
  -- ^ control of graph display
  } deriving Show

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
  , openlock = Nothing }

type LibEnv = Map.Map LIB_NAME DGraph

-- | an empty environment
emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

emptyDGwithMVar :: IO DGraph
emptyDGwithMVar = do
  ol <- newEmptyMVar
  return $ emptyDG { openlock = Just ol }

-- | inserting a (key,value) pair into a map
insertLibEnv :: (LIB_NAME , DGraph) -> LibEnv -> LibEnv
insertLibEnv (ln , dg) lib_env  = Map.insert ln dg lib_env

-- * utility functions

-- ** for node signatures

emptyG_sign :: AnyLogic -> G_sign
emptyG_sign (Logic lid) = G_sign lid (ext_empty_signature lid) startSigId

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

-- ** for node names

emptyNodeName :: NodeName
emptyNodeName = NodeName (mkSimpleId "") "" 0

showExt :: NodeName -> String
showExt (NodeName _ s i) = s ++ if i == 0 then "" else show i

showName :: NodeName -> String
showName a@(NodeName n _ _) = let ext = showExt a in
    show n ++ if ext == "" then "" else "_" ++ ext

makeName :: SIMPLE_ID -> NodeName
makeName n = NodeName n "" 0

makeMaybeName :: Maybe SIMPLE_ID -> NodeName
makeMaybeName Nothing = emptyNodeName
makeMaybeName (Just n) = makeName n

inc :: NodeName -> NodeName
inc (NodeName n s i) = NodeName n s $ succ i

extName :: String -> NodeName -> NodeName
extName s a@(NodeName n _ _) = NodeName n (showExt a ++ s) 0

-- ** accessing node label

-- | get the origin of a non-reference node (partial)
dgn_origin :: DGNodeLab -> DGOrigin
dgn_origin = node_origin . nodeInfo

-- | get the referenced library (partial)
dgn_libname :: DGNodeLab -> LIB_NAME
dgn_libname = ref_libname . nodeInfo

-- | get the referenced node (partial)
dgn_node :: DGNodeLab -> Node
dgn_node = ref_node . nodeInfo

-- | get the signature of a node's theory (total)
dgn_sign :: DGNodeLab -> G_sign
dgn_sign dn = case dgn_theory dn of
    G_theory lid sig ind _ _-> G_sign lid sig ind

-- | gets the name of a development graph node as a string (total)
getDGNodeName :: DGNodeLab -> String
getDGNodeName = showName . dgn_name

-- ** creating node content and label

-- | create default content
newNodeInfo :: DGOrigin -> DGNodeInfo
newNodeInfo orig = DGNode
  { node_origin = orig
  , node_cons_status = Nothing }

-- | create a reference node part
newRefInfo :: LIB_NAME -> Node -> DGNodeInfo
newRefInfo ln n = DGRef
  { ref_libname = ln
  , ref_node = n }

-- | create a new node label
newInfoNodeLab :: NodeName -> DGNodeInfo -> G_theory -> DGNodeLab
newInfoNodeLab name info gTh = DGNodeLab
  { dgn_name = name
  , dgn_theory = gTh
  , dgn_nf = Nothing
  , dgn_sigma = Nothing
  , nodeInfo = info
  , dgn_lock = Nothing }

-- | create a new node label using 'newNodeInfo' and 'newInfoNodeLab'
newNodeLab :: NodeName -> DGOrigin -> G_theory -> DGNodeLab
newNodeLab name orig = newInfoNodeLab name $ newNodeInfo orig

-- ** handle the lock of a node

-- | wrapper to access the maybe lock
treatNodeLock :: (MVar () -> a) -> DGNodeLab -> a
treatNodeLock f = maybe (error "MVar not initialised") f . dgn_lock

{- | Acquire the local lock. If already locked it waits till it is unlocked
     again.-}
lockLocal :: DGNodeLab -> IO ()
lockLocal = treatNodeLock $ flip putMVar ()

-- | Tries to acquire the local lock. Return False if already acquired.
tryLockLocal :: DGNodeLab -> IO Bool
tryLockLocal = treatNodeLock $ flip tryPutMVar ()

-- | Releases the local lock.
unlockLocal :: DGNodeLab -> IO ()
unlockLocal = treatNodeLock $ \ lock ->
  tryTakeMVar lock >>= maybe (error "Local lock wasn't locked.") return

-- | checks if locking MVar is initialized
hasLock :: DGNodeLab -> Bool
hasLock = maybe False (const True) . dgn_lock

-- ** handle edge numbers and proof bases

-- | create a default ID which has to be changed when inserting a certain edge.
defaultEdgeId :: EdgeId
defaultEdgeId = EdgeId (-1)

emptyProofBasis :: ProofBasis
emptyProofBasis = ProofBasis Set.empty

nullProofBasis :: ProofBasis -> Bool
nullProofBasis = Set.null . proofBasis

addEdgeId :: ProofBasis -> EdgeId -> ProofBasis
addEdgeId (ProofBasis s) e = ProofBasis $ Set.insert e s

-- | checks if the given edge is contained in the given proof basis..
roughElem :: LEdge DGLinkLab -> ProofBasis -> Bool
roughElem (_, _, label) = Set.member (dgl_id label) . proofBasis

-- ** edge label equalities

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

-- | equality comparing ids only
eqDGLinkLabById :: DGLinkLab -> DGLinkLab -> Bool
eqDGLinkLabById l1 l2 = let
    i1 = dgl_id l1
    i2 = dgl_id l2
    in if i1 > defaultEdgeId && i2 > defaultEdgeId then i1 == i2 else
       error "eqDGLinkLabById"

-- ** setting index maps

setSigMapDG :: Map.Map SigId G_sign -> DGraph -> DGraph
setSigMapDG m dg = dg { sigMap = m }

setThMapDG :: Map.Map ThId G_theory -> DGraph -> DGraph
setThMapDG m dg = dg { thMap = m }

setMorMapDG :: Map.Map MorId G_morphism -> DGraph -> DGraph
setMorMapDG m dg = dg { morMap = m }

-- ** looking up in index maps

lookupSigMapDG :: SigId -> DGraph -> Maybe G_sign
lookupSigMapDG i = Map.lookup i . sigMap

lookupThMapDG :: ThId -> DGraph -> Maybe G_theory
lookupThMapDG i = Map.lookup i . thMap

lookupMorMapDG :: MorId -> DGraph -> Maybe G_morphism
lookupMorMapDG i = Map.lookup i . morMap

-- ** getting index maps and their maximal index

getMapAndMaxIndex :: Ord k => k -> (b -> Map.Map k a) -> b -> (Map.Map k a, k)
getMapAndMaxIndex c f gctx =
    let m = f gctx in (m, if Map.null m then c else fst $ Map.findMax m)

sigMapI :: DGraph -> (Map.Map SigId G_sign, SigId)
sigMapI = getMapAndMaxIndex startSigId sigMap

thMapI :: DGraph -> (Map.Map ThId G_theory, ThId)
thMapI = getMapAndMaxIndex startThId thMap

morMapI :: DGraph -> (Map.Map MorId G_morphism, MorId)
morMapI = getMapAndMaxIndex startMorId morMap

-- ** lookup other graph parts

lookupGlobalEnvDG :: SIMPLE_ID -> DGraph -> Maybe GlobalEntry
lookupGlobalEnvDG sid = Map.lookup sid . globalEnv

-- | lookup a referenced node with a node id
lookupInRefNodesDG :: Node -> DGraph -> Maybe (LIB_NAME, Node)
lookupInRefNodesDG n = Map.lookup n . refNodes

-- | look up a refernced node with its parent infor.
lookupInAllRefNodesDG :: DGNodeInfo -> DGraph -> Maybe Node
lookupInAllRefNodesDG ref = case ref of
    DGRef { ref_libname = libn, ref_node = refn } ->
        Map.lookup (libn, refn) . allRefNodes
    _ -> error "lookupInAllRefNodesDG"

-- ** treat reference nodes

-- | add a new referenced node into the refNodes map of the given DG
addToRefNodesDG :: Node -> DGNodeInfo -> DGraph -> DGraph
addToRefNodesDG n ref dg = case ref of
    DGRef { ref_libname = libn, ref_node = refn } ->
      dg { refNodes = Map.insert n (libn, refn) $ refNodes dg
         , allRefNodes = Map.insert (libn, refn) n $ allRefNodes dg }
    _ -> error "addToRefNodesDG"

-- | delete the given referenced node out of the refnodes map
deleteFromRefNodesDG :: Node -> DGraph -> DGraph
deleteFromRefNodesDG n dg = dg { refNodes = Map.delete n $ refNodes dg }

-- ** accessing the actual graph

-- | get the next available node id
getNewNodeDG :: DGraph -> Node
getNewNodeDG = Tree.getNewNode . dgBody

-- | get all the nodes
labNodesDG :: DGraph -> [LNode DGNodeLab]
labNodesDG = labNodes . dgBody

-- | get all the edges
labEdgesDG :: DGraph -> [LEdge DGLinkLab]
labEdgesDG = labEdges . dgBody

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

-- | get the name of a node from the number of node
getNameOfNode :: Node -> DGraph -> String
getNameOfNode index gc = getDGNodeName $ labDG gc index

-- | gets the given number of new node-ids in a given DG.
newNodesDG :: Int -> DGraph -> [Node]
newNodesDG n = newNodes n . dgBody

-- ** decompose the actual graph

-- | tear the given DGraph appart.
matchDG :: Node -> DGraph -> (MContext DGNodeLab DGLinkLab, DGraph)
matchDG n dg = let (mc, b) = match n $ dgBody dg in(mc, dg { dgBody = b })

-- | get the context of the given DG
contextDG :: DGraph -> Node -> Context DGNodeLab DGLinkLab
contextDG = context . dgBody

-- | safe context for graphs
safeContext :: (Show a, Show b, Graph gr) => String -> gr a b -> Node
            -> Context a b
safeContext err g v =
  maybe (error $ err ++ ": Match Exception, Node: " ++ show v) id
  $ fst $ match v g

-- | get the context and throw input string as error message
safeContextDG :: String -> DGraph -> Node -> Context DGNodeLab DGLinkLab
safeContextDG s dg n = safeContext s (dgBody dg) n

-- ** manipulate graph

-- | sets the node with new label and returns the new graph and the old label
labelNodeDG :: LNode DGNodeLab -> DGraph -> (DGraph, DGNodeLab)
labelNodeDG p g =
    let (b, l) = Tree.labelNode p $ dgBody g in (g { dgBody = b }, l)

-- | delete the node out of the given DG
delNodeDG :: Node -> DGraph -> DGraph
delNodeDG n dg = dg { dgBody = delNode n $ dgBody dg }

-- | delete the LNode out of the given DG
delLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
delLNodeDG n dg = dg { dgBody = Tree.delLNode (==) n $ dgBody dg }

-- | delete a list of nodes out of the given DG
delNodesDG :: [Node] -> DGraph -> DGraph
delNodesDG ns dg = dg { dgBody = delNodes ns $ dgBody dg }

-- | insert a new node into given DGraph
insNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insNodeDG n dg = dg { dgBody = insNode n $ dgBody dg }

-- | inserts a lnode into a given DG
insLNodeDG :: LNode DGNodeLab -> DGraph -> DGraph
insLNodeDG n@(v, _) g =
    if gelemDG v g then error $ "insLNodeDG " ++ show v else insNodeDG n g

-- | insert a new node with the given node content into a given DGraph
insNodesDG :: [LNode DGNodeLab] -> DGraph -> DGraph
insNodesDG ns dg = dg { dgBody = insNodes ns $ dgBody dg }

-- | delete an edge out of a given DG
delEdgeDG :: Edge -> DGraph -> DGraph
delEdgeDG e dg = dg { dgBody = delEdge e $ dgBody dg }

-- | delete a list of edges
delEdgesDG :: [Edge] -> DGraph -> DGraph
delEdgesDG es dg = dg { dgBody = delEdges es $ dgBody dg }

-- | delete a labeled edge out of the given DG
delLEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
delLEdgeDG e g = g
    { dgBody = Tree.delLEdge (\ l1 l2 -> compare (dgl_id l1) $ dgl_id l2) e
      $ dgBody g }

-- | insert a labeled edge into a given DG, return possibly new id of edge
insLEdgeDG :: LEdge DGLinkLab -> DGraph -> (LEdge DGLinkLab, DGraph)
insLEdgeDG (s, t, l) g =
  let eId = dgl_id l
      nId = getNewEdgeId g
      newId = dgl_id l == defaultEdgeId
      e = (s, t, if newId then l { dgl_id = nId } else l)
  in (e, g
    { getNewEdgeId = if newId then succ nId else max nId $ succ eId
    , dgBody = fst $ Tree.insLEdge True (\ l1 l2 ->
        if eqDGLinkLabContent l1 { dgl_id = defaultEdgeId } l2
        then EQ else compare (dgl_id l1) $ dgl_id l2) e $ dgBody g })

{- | tries to insert a labeled edge into a given DG, but if this edge
     already exists, then does nothing. -}
insLEdgeNubDG :: LEdge DGLinkLab -> DGraph -> DGraph
insLEdgeNubDG (v, w, l) g =
  let oldEdgeId = getNewEdgeId g
      (ng, change) = Tree.insLEdge False (\ l1 l2 ->
        if eqDGLinkLabContent l1 { dgl_id = defaultEdgeId } l2
        then EQ else compare (dgl_id l1) $ dgl_id l2)
        (v, w, l { dgl_id = oldEdgeId }) $ dgBody g
  in
     g { getNewEdgeId = if change then succ oldEdgeId else oldEdgeId
       , dgBody = ng }

{- | insert an edge into the given DGraph, which updates
     the graph body and the edge counter as well. -}
insEdgeDG :: LEdge DGLinkLab -> DGraph -> DGraph
insEdgeDG l oldDG =
  oldDG { dgBody = insEdge l $ dgBody oldDG
        , getNewEdgeId = succ $ getNewEdgeId oldDG }

-- | insert a list of labeled edge into a given DG
insEdgesDG :: [LEdge DGLinkLab] -> DGraph -> DGraph
insEdgesDG = flip $ foldr insEdgeDG

-- | merge a list of lnodes and ledges into a given DG
mkGraphDG :: [LNode DGNodeLab] -> [LEdge DGLinkLab] -> DGraph -> DGraph
mkGraphDG ns ls dg = insEdgesDG ls $ insNodesDG ns dg

-- ** handle proof history

-- | add a proof history into current one of the given DG
setProofHistoryDG :: ProofHistory -> DGraph -> DGraph
setProofHistoryDG h dg = dg { proofHistory = h ++ proofHistory dg }

-- | add a history item to current history.
addToProofHistoryDG :: ([DGRule], [DGChange]) -> DGraph -> DGraph
addToProofHistoryDG x dg = dg { proofHistory = x : proofHistory dg }

-- | update the proof history with a function
setProofHistoryWithDG :: (ProofHistory -> ProofHistory)
                      -> DGraph -> DGraph
setProofHistoryWithDG f dg = dg { proofHistory = f $ proofHistory dg }

-- ** top-level functions

-- | initializes the MVar for locking if nessesary
initLocking :: DGraph -> LNode DGNodeLab -> IO (DGraph, DGNodeLab)
initLocking dg (node, dgn) = do
  lock <- newEmptyMVar
  let dgn' = dgn { dgn_lock = Just lock }
  return (fst $ labelNodeDG (node, dgn') dg, dgn')

-- | returns the DGraph that belongs to the given library name
lookupDGraph :: LIB_NAME -> LibEnv -> DGraph
lookupDGraph ln = Map.findWithDefault (error "lookupDGraph") ln


--moved to make THs work

-- determines the morphism of a given path
calculateMorphismOfPath :: [LEdge DGLinkLab] -> Maybe GMorphism
calculateMorphismOfPath p = case p of
  (_, _, lbl) : r -> let morphism = dgl_morphism lbl in
    if null r then Just morphism else do
       rmor <- calculateMorphismOfPath r
       resultToMaybe $ compInclusion logicGraph morphism rmor
  [] -> error "calculateMorphismOfPath"


isGlobalDef :: DGLinkType -> Bool
isGlobalDef lt = case lt of
    GlobalDef -> True
    _ -> False

liftE :: (DGLinkType -> Bool) -> LEdge DGLinkLab -> Bool
liftE f (_, _, edgeLab) = f $ dgl_type edgeLab

-- | or two predicates
liftOr :: (a -> Bool) -> (a -> Bool) -> a -> Bool
liftOr f g x = f x || g x



{- compute the theory of a given node.
   If this node is a DGRef, the referenced node is looked up first. -}
computeLocalTheory :: Monad m => LibEnv -> LIB_NAME -> Node -> m G_theory
computeLocalTheory libEnv ln node =
  if isDGRef nodeLab
    then
      computeLocalTheory libEnv refLn $ dgn_node nodeLab
    else return $ dgn_theory nodeLab
    where
      dgraph = lookupDGraph ln libEnv
      nodeLab = labDG dgraph node
      refLn = dgn_libname nodeLab

isLocalDef :: DGLinkType -> Bool
isLocalDef lt = case lt of
    LocalDef -> True
    _ -> False

