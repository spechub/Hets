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
 ( Token (..)
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
 , defaultHetcatsOpts -- :: HetcatsOpts
 , read_and_analyse -- :: String -> HetcatsOpts -> IO (Maybe (LibName, LibEnv))
 , computeTheory -- :: LibEnv -> LibName -> Node -> Maybe G_theory
 , DGRule  (..)
 , ThmLinkStatus (..) 
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

-- | proof status of a link
data ThmLinkStatus = LeftOpen | Proven DGRule ProofBasis
  deriving (Show, Eq, Ord, Typeable, Data)
-}
{- | automatically applies all rules to the library
   denoted by the library name of the given proofstatus -}
 , automatic -- :: LibName -> LibEnv -> LibEnv
 , automaticFromList -- :: LibName -> [LEdge DGLinkLab] -> LibEnv -> LibEnv
   
{-
  , genSelectCmd Node cDgSelect
  , genSelectCmd ComorphismTranslation cTranslate
  , genSelectCmd Prover cProver
  , genSelectCmd Goal $ cGoalsAxmGeneral ActionSet ChangeGoals
  , proveAll
  , disproveAll
  , genGlobCmd CheckConsistencyCurrent cConsistCheck
  , genGlobCmd CheckConservativityAll cConservCheckAll
  , genGlobCmd DropTranslation cDropTranslations
  , genSelectCmd ConsistencyChecker cConsChecker
  , genSelectCmd ConservativityCheckerOpen cConservCheck
  , genSelectCmd ConservativityChecker cConservCheck
  , genCmd (TimeLimit 0) CmdNoPriority ReqNumber $ CmdWithInput cTimeLimit
  , genCmd (SetAxioms []) CmdNoPriority (ReqAxm True) $ CmdWithInput
    $ cGoalsAxmGeneral ActionSet ChangeAxioms ]
  ++ map (\ b -> genCmd (IncludeProvenTheorems b) CmdNoPriority ReqNothing
         $ CmdNoInput $ cSetUseThms b) [True, False]
  ++
  [ genGlobInspectCmd Nodes cNodes
  , genGlobInspectCmd Edges cEdges
  , genGlobInspectCmd UndoHist cUndoHistory
  , genGlobInspectCmd RedoHist cRedoHistory
  , genGlobInspectCmd CurrentComorphism cCurrentComorphism
  , genGlobInspectCmd ProvenGoals $ cShowNodeProvenGoals ""
  , genGlobInspectCmd UnprovenGoals $ cShowNodeUnprovenGoals ""
  , genGlobInspectCmd Axioms $ cShowNodeAxioms ""
  , genGlobInspectCmd AllGoals $ cShowTheoryGoals ""
  , genGlobInspectCmd Theory $ cShowTheory Dont_translate ""
  , genGlobInspectCmd TranslatedTheory $ cShowTheory Do_translate ""
  , genGlobInspectCmd Taxonomy $ cShowTaxonomy ""
  , genGlobInspectCmd Concept $ cShowConcept ""
  , genGlobInspectCmd NodeInfo cInfoCurrent
  , genCmd (InspectCmd ComorphismsTo Nothing) CmdNoPriority ReqLogic
  . CmdWithInput $ cComorphismsTo
  , genInspectCmd NodeInfo cInfo
  , genInspectCmd Theory $ cShowTheory Dont_translate
  , genInspectCmd TranslatedTheory $ cShowTheory Do_translate
  , genInspectCmd AllGoals cShowTheoryGoals
  , genInspectCmd ProvenGoals cShowNodeProvenGoals
  , genInspectCmd UnprovenGoals cShowNodeUnprovenGoals
  , genInspectCmd Axioms cShowNodeAxioms
  , genInspectCmd Taxonomy cShowTaxonomy
  , genInspectCmd Concept cShowConcept
  , genInspectCmd EdgeInfo cInfo ]
-}
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
