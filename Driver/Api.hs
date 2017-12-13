{-# LANGUAGE CPP #-}
{- |
Module      :  ./Driver/Api.hs
Description :  Haskell API for Hets 
Copyright   :  (c) Till Mossakowski, Uni Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iks.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable

Haskell API for Hets. Contains all Haskell datatypes and functions that
are necessary to interact with Hets from the outside
-}

module Driver.Api
 (
-----------------
-- Identifiers --
-----------------
   Token (..)
 , SIMPLE_ID
{-
-- | tokens as supplied by the scanner
data Token = Token { tokStr :: String
                   , tokPos :: Range
                   } deriving (Eq, Ord, Typeable, Data)
-- | simple ids are just tokens
type SIMPLE_ID = Token
-}
 , LibName (..)
{-
data LibName = LibName
    { getLibId :: IRI
    , locIRI :: Maybe IRI
    , mimeType :: Maybe String
    , libVersion :: Maybe VersionNumber }
  deriving (Typeable, Data)
-}

--------------------------------
-- Options (for calling Hets) --
--------------------------------

 , CASLAmalgOpt (..)
{-   
data CASLAmalgOpt = Sharing         -- ^ perform the sharing checks
    | ColimitThinness -- ^ perform colimit thinness check (implies Sharing)
    | Cell            -- ^ perform cell condition check (implies Sharing)
    | NoAnalysis      -- ^ dummy option to indicate empty option string
-}
 , AnaType (..)
{-   
-- | 'AnaType' describes the type of analysis to be performed
data AnaType = Basic | Structured | Skip
-}
 , GuiType (..)
{-   
-- | 'GuiType' determines if we want the GUI shown
data GuiType = UseGui | NoGui
  deriving Eq
-}
 , HetcatsOpts (..)
{-
-- | 'HetcatsOpts' is a record of all options received from the command line
data HetcatsOpts = HcOpt     -- for comments see usage info
  { analysis :: AnaType
  , guiType :: GuiType
  , urlCatalog :: [(String, String)]
  , infiles :: [FilePath] -- ^ files to be read
  , specNames :: [SIMPLE_ID] -- ^ specs to be processed
  , transNames :: [SIMPLE_ID] -- ^ comorphism to be processed
  , viewNames :: [SIMPLE_ID] -- ^ views to be processed
  , intype :: InType
  , libdirs :: [FilePath]
  , modelSparQ :: FilePath
  , counterSparQ :: Int
  , outdir :: FilePath
  , outtypes :: [OutType]
  , xupdate :: FilePath
  , recurse :: Bool
  , verbose :: Int
  , defLogic :: String
  , defSyntax :: String
  , outputToStdout :: Bool    -- ^ send messages to stdout?
  , caslAmalg :: [CASLAmalgOpt]
  , interactive :: Bool
  , connectP :: Int
  , connectH :: String
  , uncolored :: Bool
  , xmlFlag :: Bool
  , applyAutomatic :: Bool
  , computeNormalForm :: Bool
  , dumpOpts :: [String]
  , disableCertificateVerification :: Bool
  , ioEncoding :: Enc
    -- | use the library name in positions to avoid differences after uploads
  , useLibPos :: Bool
  , unlit :: Bool
  , serve :: Bool
  , listen :: Int
  , pidFile :: FilePath
  , whitelist :: [[String]]
  , blacklist :: [[String]]
  , runMMT :: Bool
  , fullTheories :: Bool
  , outputLogicList :: Bool
  , outputLogicGraph :: Bool
  , fileType :: Bool
  , accessToken :: String
  , httpRequestHeaders :: [String]
  , fullSign :: Bool
  , printAST :: Bool }
-}
 , defaultHetcatsOpts -- :: HetcatsOpts

--------------------------------------------
-- Development graph, library environment --
--------------------------------------------

 , LibEnv
{-   
type LibEnv = Map.Map LibName DGraph
-}
 , DGraph (..)
 , DGNodeLab (..)
 , DGNodeInfo (..)
 , DGLinkLab (..)
 , DGLinkType (..)
 , RTLinkLab (..)
 , RTLinkType (..)
{-
{- | the actual development graph with auxiliary information. A
  'G_sign' should be stored in 'sigMap' under its 'gSignSelfIdx'. The
  same applies to 'G_morphism' with 'morMap' and 'gMorphismSelfIdx'
  resp. 'G_theory' with 'thMap' and 'gTheorySelfIdx'. -}
data DGraph = DGraph
  { globalAnnos :: GlobalAnnos -- ^ global annos of library
  , optLibDefn :: Maybe LIB_DEFN
  , globalEnv :: GlobalEnv -- ^ name entities (specs, views) of a library
  , dgBody :: Tree.Gr DGNodeLab DGLinkLab  -- ^ actual 'DGraph` tree
  , currentBaseTheory :: Maybe NodeSig
  , refTree :: Tree.Gr RTNodeLab RTLinkLab -- ^ the refinement tree
  , specRoots :: Map.Map String Node -- ^ root nodes for named specs
  , nameMap :: MapSet.MapSet String Node -- ^ all nodes by name
  , archSpecDiags :: Map.Map String Diag
      -- ^ dependency diagrams between units
  , getNewEdgeId :: EdgeId  -- ^ edge counter
  , allRefNodes :: Map.Map (LibName, Node) Node -- ^ all DGRef's
  , sigMap :: Map.Map SigId G_sign -- ^ signature map
  , thMap :: Map.Map ThId G_theory -- ^ theory map
  , morMap :: Map.Map MorId G_morphism -- ^ morphism map
  , proofHistory :: ProofHistory -- ^ applied proof steps
  , redoHistory :: ProofHistory -- ^ undone proofs steps
  } deriving Typeable
-- | node content or reference to another library's node
data DGNodeInfo = DGNode
  { node_origin :: DGOrigin       -- origin in input language
  , node_cons_status :: ConsStatus } -- like a link from the empty signature
  | DGRef                        -- reference to node in a different DG
  { ref_libname :: LibName      -- pointer to DG where ref'd node resides
  , ref_node :: Node             -- pointer to ref'd node
  } deriving (Show, Eq, Typeable)

{- | node inscriptions in development graphs.
Nothing entries indicate "not computed yet" -}
data DGNodeLab =
  DGNodeLab
  { dgn_name :: NodeName        -- name in the input language
  , dgn_theory :: G_theory      -- local theory
  , globalTheory :: Maybe G_theory -- global theory
  , labelHasHiding :: Bool      -- has this node an ingoing hiding link
  , labelHasFree :: Bool        -- has incoming free definition link
  , dgn_nf :: Maybe Node         -- normal form, for Theorem-Hide-Shift
  , dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature
  , dgn_freenf :: Maybe Node -- normal form for freeness
  , dgn_phi :: Maybe GMorphism -- morphism from signature to nffree signature
  , nodeInfo :: DGNodeInfo
  , nodeMod :: NodeMod
  , xnode :: Maybe XGraph.XNode
  , dgn_lock :: Maybe (MVar ())
  } deriving Typeable
-- | link inscriptions in development graphs
data DGLinkLab = DGLink
  { dgl_morphism :: GMorphism  -- signature morphism of link
  , dgl_type :: DGLinkType     -- type: local, global, def, thm?
  , dgl_origin :: DGLinkOrigin -- origin in input language
  , dglPending :: Bool        -- open proofs of edges in proof basis
  , dgl_id :: EdgeId          -- id of the edge
  , dglName :: String         -- name of the edge
  } deriving (Eq, Typeable)
{- | Link types of development graphs,
     Sect. IV:4.2 of the CASL Reference Manual explains them in depth. -}
data DGLinkType =
    ScopedLink Scope LinkKind ConsStatus
  | HidingDefLink
  | FreeOrCofreeDefLink FreeOrCofree MaybeNode -- the "parameter" node
  | HidingFreeOrCofreeThm (Maybe FreeOrCofree) Node GMorphism ThmLinkStatus
    {- DGLink S1 S2 m2 (DGLinkType m1 p) n
    corresponds to a span of morphisms
    S1 <--m1-- S --m2--> S2 -}
    deriving (Show, Eq, Typeable)
data RTLinkType =
    RTRefine
  | RTComp
  deriving (Show, Eq, Typeable)

data RTLinkLab = RTLink
  { rtl_type :: RTLinkType
  } deriving (Show, Eq, Typeable)
-}

-----------------------------------
-- Hets' main analysis functions --
-----------------------------------
   
 , read_and_analyse -- :: String -> HetcatsOpts -> IO (Maybe (LibName, LibEnv))
 , computeTheory -- :: LibEnv -> LibName -> Node -> Maybe G_theory

---------------------------------------
-- Basic proofs (in specific logics) --
---------------------------------------
 , BasicProof (..)
{-
data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (ProofStatus proof_tree)
     | Guessed
     | Conjectured
     | Handwritten
     deriving Typeable
-}
   
--------------------------------------
-- Development graph proof calculus --
--------------------------------------

 , DGRule  (..)
{-   
{- | Rules in the development graph calculus,
   Sect. IV:4.4 of the CASL Reference Manual explains them in depth
-}
data DGRule =
    DGRule String
  | DGRuleWithEdge String EdgeId
  | DGRuleLocalInference [(String, String)] -- renamed theorems
  | Composition [EdgeId]
    deriving (Show, Eq, Ord, Typeable, Data)
-}
 , ThmLinkStatus (..) 
{-
-- | proof status of a link
data ThmLinkStatus = LeftOpen | Proven DGRule ProofBasis
  deriving (Show, Eq, Ord, Typeable, Data)
-}
{- | automatically applies all rules to the library
   denoted by the library name of the given proofstatus -}
 , automatic -- :: LibName -> LibEnv -> LibEnv
 , automaticFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
{- | gets all unproven global theorem edges in the current development graph
   and checks, if they are a composition of a global theorem path. If so,
   the edge is proven, with the corresponding path as its proof basis.
   If there is more than one path, the first of them is arbitrarily taken. -}
 , composition -- :: LibName -> LibEnv -> LibEnv
{- | creates new edges by composing all paths of global theorem edges
   in the current development graph. These new edges are proven global
   theorems with the morphism and the conservativity of the corresponding
   path. If a new edge is the proven version of a previsously existing
   edge, that edge is deleted. -}
 , compositionCreatingEdges -- :: LibName -> LibEnv -> LibEnv
-- | composition without creating new new edges
 , compositionFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
 , compositionCreatingEdgesFromList
     -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
-- | tries to apply global subsumption to all unproven global theorem edges
 , globSubsume -- :: LibName -> LibEnv -> LibEnv
{- applies global decomposition to all unproven global theorem edges
   if possible -}
 , globDecomp -- :: LibName -> LibEnv -> LibEnv
{- | applies global decomposition to the list of edges given (global
     theorem edges) if possible, if empty list is given then to all
     unproven global theorems.
-}
 , globDecompFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
-- | applies global subsumption to a list of global theorem edges
 , globSubsumeFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
-- | applies hide-theorem-shift rule
 , interactiveHideTheoremShift -- :: LibName -> LibEnv -> IO LibEnv
 , automaticHideTheoremShift -- :: LibName -> LibEnv -> LibEnv
 , automaticHideTheoremShiftFromList
      --  :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
{- | applies basic inference to a given node. The result is a theory which is
     either a model after a consistency check or a new theory for the node
     label -}
 , basicInferenceNode -- :: LogicGraph -> LibName -> DGraph -> LNode DGNodeLab
                      --     -> LibEnv -> IORef IntState
                      --     -> IO (Result G_theory)
-- | local inference for all edges
 , localInference -- :: LibName -> LibEnv -> LibEnv
-- | local inference for some edges
 , localInferenceFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
-- | local decomposition for all edges
 , locDecomp -- :: LibName -> LibEnv -> LibEnv
-- | local decomposition for some edges
 , locDecompFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
-- | apply rule theorem hide shift to a development graph
 , theoremHideShift -- :: LibName -> LibEnv -> Result LibEnv
-- | apply rule theorem hide shift to a DGs in LibEnv
 , theoremHideShiftFromList -- :: LibName -> [LNode DGNodeLab] -> LibEnv
                            --     -> Result LibEnv
-- | the theorem hide shift rule name
 , thmHideShift -- :: DGRule
{- | get all the global unproven threorem links which go into the given
     node in the given dgraph
-}
 , getInComingGlobalUnprovenEdges -- :: DGraph -> Node -> [LEdge DGLinkLab]
-- | the triangle consistency rule name   
 , triangleConsRule -- :: DGRule
-- | apply rule triangle consistency rule to a development graph
 , triangleCons -- :: LibName -> LibEnv -> Result LibEnv
-- | apply rule triangle consistency rule to one edge (?)
 , triangleConsDG -- :: DGraph -> LEdge DGLinkLab -> Result DGraph
-- | applies basic inference with VSE to a given node and whole import tree above
 , proveVSE -- :: (LibName, Node) -> LibEnv -> IO (Result LibEnv)


----------------------------------------------------------------
-- Development graph rules for consistency and conservativity --
----------------------------------------------------------------

-- calls various rules for checking conservativity of links
 , conservativity -- :: LibName -> LibEnv -> LibEnv
-- data types for result of consistency checks   
 , SType (..)
{- data SType = CSUnchecked
           | CSTimeout
           | CSError
           | CSInconsistent
           | CSConsistent
           deriving (Eq, Ord, Show)
-}
 , ConsistencyStatus (..)
{- data ConsistencyStatus = ConsistencyStatus { sType :: SType
                                           , sMessage :: String }
-}
-- invert: consistent becomes inconsistent, and vice versa
 , cInvert -- :: ConsistencyStatus -> ConsistencyStatus
-- devGraph rule that calls consistency checker for specific logics
 , consistencyCheck -- :: Bool -> G_cons_checker -> AnyComorphism -> LibName -> LibEnv
                     --    -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus
-- convert a consistency status to a color (of the DG node)    
 , cStatusToColor -- :: ConsistencyStatus -> String
-- convert a consistency status to a prefix, for use in a GUI,
-- to be displayed in front of the node name 
 , cStatusToPrefix -- :: ConsistencyStatus -> String
{- converts a GTheory.BasicProof to ConsistencyStatus.
The conversion is not exact, but sufficient since this function is only
implemented in GtkDisprove for proper display of goalstatus.
-}
 , basicProofToConStatus --  :: BasicProof -> ConsistencyStatus
-- roughly transform the nodes consStatus into ConsistencyStatus
 , getConsistencyOf --  :: DGNodeLab -> ConsistencyStatus

-------------------------------------------
-- Flattening out structuring operations --
-------------------------------------------

{- this function performs flattening of import link by deleting all
   inclusion links, and inserting a new node, with new computed theory
   (computeTheory).
-}
 , dgFlatImports -- :: LibEnv -> LibName -> DGraph -> DGraph
-- this function performs flattening of imports for the whole library
 , libFlatImports -- :: LibEnv -> Result LibEnv
{- this function performs flattening of non-disjoint unions for the given
   DGraph. 
-}
 , dgFlatDUnions -- :: LibEnv -> DGraph -> DGraph
{- this functions performs flattening of
   non-disjoint unions for the whole library -}
 , libFlatDUnions -- :: LibEnv -> Result LibEnv
{- this function performs flattening of imports with renaming
   links for a given developement graph.
-}
 , dgFlatRenamings -- :: LibEnv -> LibName -> DGraph -> DGraph
-- this function performs flattening of imports with renamings
 , libFlatRenamings -- :: LibEnv -> Result LibEnv
-- this function performs flattening of hiding links
 , dgFlatHiding -- :: DGraph -> DGraph
-- this function performs flattening of heterogeniety for the whole library
 , libFlatHiding -- :: LibEnv -> Result LibEnv
{- this function performs flattening of heterogeniety
for a given developement graph -}
 , dgFlatHeterogen -- :: LibEnv -> LibName -> DGraph -> DGraph
-- this function performs flattening of heterogeniety for the whole library
 , libFlatHeterogen -- :: LibEnv -> Result LibEnv
{- this function takes a node and performs flattening
of non-disjoint unions for the ingoing tree of nodes to the given node -}
 , singleTreeFlatDUnions -- :: LibEnv -> LibName -> Node -> Result LibEnv
    
-------------------------------
-- Normal forms and colimits --
-------------------------------
   
-- | compute normal form for a library and imported libs
 , normalForm -- :: LibName -> LibEnv -> Result LibEnv
-- | compute norm form for all libraries
 , normalFormLibEnv -- :: LibEnv -> Result LibEnv
-- the normal form rule name  
 , normalFormRule -- :: DGRule
-- | computes the colimit of one development graph in a LibEnv
 , computeColimit -- :: LibName -> LibEnv -> Result LibEnv
-- compute normal forms for nodes with free definition links
 , freeness -- :: LibName -> LibEnv -> Result LibEnv

   
-- todo
   -- BasicProof
   -- Proofs.StatusUtils?
 ) where

import Common.Amalgamate (CASLAmalgOpt (..))
import Common.Id (Token (..), SIMPLE_ID)
import Common.LibName

import Static.DevGraph (LibEnv, DGraph (..), DGNodeLab (..), DGNodeInfo (..),
                        DGLinkLab (..), DGLinkType (..), 
                        RTLinkType (..), RTLinkLab (..))
import Driver.Options (AnaType (..), GuiType (..), HetcatsOpts (..),
                       defaultHetcatsOpts)

import Driver.ReadMain (read_and_analyse) 

import Static.ComputeTheory (computeTheory)

import Static.DgUtils (DGRule  (..), ThmLinkStatus (..))

import Proofs.Automatic (automatic, automaticFromList)
import Proofs.Composition
          (composition, compositionCreatingEdges,
           compositionFromList, compositionCreatingEdgesFromList)
import Proofs.ComputeColimit (computeColimit)
import Proofs.Conservativity (conservativity)
import Proofs.ConsistencyCheck
       (consistencyCheck, SType (..), ConsistencyStatus (..),
        cStatusToColor, cStatusToPrefix, cInvert, basicProofToConStatus,
        getConsistencyOf)
import Proofs.DGFlattening
       (dgFlatImports, libFlatImports , dgFlatDUnions, libFlatDUnions,
        dgFlatRenamings, libFlatRenamings, dgFlatHiding, libFlatHiding,
        dgFlatHeterogen, libFlatHeterogen, singleTreeFlatDUnions)
import Proofs.Freeness (freeness)
import Proofs.Global (globSubsume, globDecomp, 
                      globDecompFromList, globSubsumeFromList)
import Proofs.HideTheoremShift
    (interactiveHideTheoremShift, automaticHideTheoremShift,
     automaticHideTheoremShiftFromList)
import Proofs.InferBasic (basicInferenceNode)
import Proofs.Local
    (localInference, locDecomp, locDecompFromList, localInferenceFromList)
import Proofs.NormalForm
    (normalFormLibEnv, normalForm, normalFormRule) 
import Proofs.SimpleTheoremHideShift
    (thmHideShift, getInComingGlobalUnprovenEdges)
import Proofs.TheoremHideShift
    (theoremHideShift, theoremHideShiftFromList)
import Proofs.TriangleCons 
import Proofs.VSE 
import Static.GTheory (BasicProof (..))
