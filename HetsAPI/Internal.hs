{- |
Description :  This module aims to bundle all internals required to work with the API. The main reason is for the Python API to only import to modules.
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}

module HetsAPI.Internal (
    fromJust
    , Result, resultToMaybe, Diagnosis
    , HetcatsOpts(..), defaultHetcatsOpts
    , DGraph, DGNodeLab, DGLinkLab()
    , DGNodeType, nodeTypeIsProven, nodeTypeIsProvenConsistent, nodeTypeIsReference
    , DevGraphLinkType(..), DevGraphLinkKind(..), getDevGraphLinkType
    -- , DGEdgeType, edgeTypeModInc, edgeTypeisInc
    -- , DGEdgeTypeModInc, GlobalDef, HetDef, HidingDef, LocalDef, FreeOrCofreeDef, ThmType, thmEdgeType, isProvenEdge, isConservativ, isPending
    , developmentGraphNodeLabelName
    , developmentGraphEdgeLabelName
    , developmentGraphEdgeLabelId
    , ProofStatus(..)
    , GoalStatus(..)
    , TimeOfDay
    , TacticScript
    , tacticScriptContent
    , ProofState
    , ConsistencyStatus
    , consistencyStatusType
    , consistencyStatusMessage
    , SType(..)
    , ConsStatus
    , requiredConservativity
    , provenConservativity
    , linkStatus
    , Conservativity(..)
    , getNodeConsStatus
    , getConsOfStatus
    , isProvenConsStatusLink
    , showConsistencyStatus
    , isInternalNode
    , referencedNodeLibName
    , isNodeReferenceNode
    , ExtSign
    , plainSign
    , nonImportedSymbols
    , GlobalAnnos
    , globalAnnotations
    , precedenceAnnotations
    , associativityAnnotations
    , displayAnnos
    , literalAnnos
    , prefixMap
    , LiteralType

    , Token
    , Id

    , LibName(..)
    , getFilePath
    , LibEnv

    , IRI

    , showGlobalDoc
    , showDoc

    -- , optsWithAnalysis
    -- , optsWithGuiType
    , optsWithUrlCatalog
    , optsWithInfiles
    , optsWithSpecNames
    , optsWithTransNames
    , optsWithLossyTrans
    , optsWithViewNames
    -- , optsWithIntype
    , optsWithLibdirs
    , optsWithModelSparQ
    , optsWithCounterSparQ
    , optsWithOutdir
    -- , optsWithOuttypes
    , optsWithDatabaseDoMigrate
    , optsWithDatabaseOutputFile
    , optsWithDatabaseConfigFile
    , optsWithDatabaseSubConfigKey
    , optsWithDatabaseFileVersionId
    , optsWithDatabaseReanalyze
    -- , optsWithDatabaseConfig
    -- , optsWithDatabaseContext
    , optsWithXupdate
    , optsWithRecurse
    , optsWithVerbose
    , optsWithDefLogic
    , optsWithDefSyntax
    , optsWithOutputToStdout
    -- , optsWithCaslAmalg
    , optsWithInteractive
    , optsWithConnectP
    , optsWithConnectH
    , optsWithUncolored
    , optsWithXmlFlag
    , optsWithApplyAutomatic
    , optsWithComputeNormalForm
    , optsWithDumpOpts
    , optsWithDisableCertificateVerification
    -- , optsWithIoEncoding
    , optsWithUseLibPos
    , optsWithUnlit
    , optsWithServe
    , optsWithListen
    , optsWithPidFile
    , optsWithWhitelist
    , optsWithBlacklist
    , optsWithRunMMT
    , optsWithFullTheories
    , optsWithOutputLogicList
    , optsWithOutputLogicGraph
    , optsWithFileType
    , optsWithAccessToken
    , optsWithHttpRequestHeaders
    , optsWithFullSign
    , optsWithPrintAST
) where


import Data.Maybe (fromJust)
import Data.Time (TimeOfDay)

import Common.DocUtils(showGlobalDoc, showDoc)
import Common.ExtSign (ExtSign(..))
import Common.Consistency(Conservativity(..), showConsistencyStatus)
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.LibName (LibName(..), getFilePath)
import Common.Result (Result, resultToMaybe, Diagnosis)
import Driver.Options (HetcatsOpts(..), defaultHetcatsOpts)
import Static.DevGraph (DGraph, DGNodeLab(..), DGLinkLab(..), DGNodeInfo(..), getNodeConsStatus, getNodeCons, getDGNodeName, globalAnnos, LibEnv, isInternalNode, getRealDGLinkType, isDGRef, dgn_libname)
import Static.DgUtils (ConsStatus(..), getConsOfStatus, isProvenConsStatusLink, NodeName, DGNodeType(..), DGEdgeType(..), DGEdgeTypeModInc(..), Scope(..), ThmTypes(..), FreeOrCofree(..), ConsStatus(..), getEdgeNum)
import Logic.Prover (ProofStatus(..), GoalStatus(..), TacticScript(..))
import Proofs.AbstractState (ProofState)
import Proofs.ConsistencyCheck (ConsistencyStatus(..), SType(..))

developmentGraphNodeLabelName :: DGNodeLab -> String
developmentGraphNodeLabelName = getDGNodeName

developmentGraphNodeConsistencyStatus :: DGNodeLab -> Maybe ConsStatus
developmentGraphNodeConsistencyStatus node = case nodeInfo node of
    DGNode _ status -> Just status
    _ -> Nothing

developmentGraphEdgeLabelName :: DGLinkLab -> String
developmentGraphEdgeLabelName = dglName

developmentGraphEdgeLabelId :: DGLinkLab -> Int
developmentGraphEdgeLabelId = getEdgeNum . dgl_id


consistencyStatusType :: ConsistencyStatus -> SType
consistencyStatusType = sType


consistencyStatusMessage :: ConsistencyStatus -> String
consistencyStatusMessage = sMessage

globalAnnotations :: DGraph -> GlobalAnnos
globalAnnotations = globalAnnos

precedenceAnnotations :: GlobalAnnos -> PrecedenceGraph
precedenceAnnotations = prec_annos

associativityAnnotations :: GlobalAnnos -> AssocMap
associativityAnnotations = assoc_annos

displayAnnos :: GlobalAnnos -> DisplayMap
displayAnnos = display_annos

literalAnnos :: GlobalAnnos -> LiteralAnnos
literalAnnos = literal_annos

prefixMap :: GlobalAnnos -> PrefixMap
prefixMap = prefix_map

nodeTypeIsProven :: DGNodeType -> Bool
nodeTypeIsProven = isProvenNode

nodeTypeIsProvenConsistent :: DGNodeType -> Bool
nodeTypeIsProvenConsistent = isProvenCons

nodeTypeIsReference :: DGNodeType -> Bool
nodeTypeIsReference = isRefType

tacticScriptContent :: TacticScript -> String
tacticScriptContent (TacticScript c) = c


data DevGraphLinkKind = LinkKindGlobal | LinkKindLocal | LinkKindHiding | LinkKindFree | LinkKindCofree
data DevGraphLinkType =
    DefinitionLink { linkTypeKind :: DevGraphLinkKind, linkTypeIsInclusion :: Bool, linkTypeIsHomogenoeous :: Bool }
     | TheoremLink { linkTypeKind :: DevGraphLinkKind, linkTypeIsInclusion :: Bool, linkTypeIsHomogenoeous :: Bool, linkTypeIsProven :: Bool, linkTypeIsConservativ :: Bool, linkTypeIsPending :: Bool }

getDevGraphLinkType :: DGLinkLab -> DevGraphLinkType
getDevGraphLinkType l = case edgeTypeModInc (getRealDGLinkType l) of
    GlobalDef -> DefinitionLink LinkKindGlobal inclusion True
    HetDef -> DefinitionLink LinkKindGlobal inclusion False
    HidingDef -> DefinitionLink LinkKindHiding inclusion True
    LocalDef -> DefinitionLink LinkKindLocal inclusion True
    FreeOrCofreeDef freeOrCofree -> DefinitionLink (case freeOrCofree of
        Free -> LinkKindFree
        Cofree -> LinkKindCofree) inclusion True
    ThmType {thmEdgeType=thmType, isProvenEdge=proven, isConservativ=conservativ, isPending=pending} -> TheoremLink kind inclusion homogeneous proven conservativ pending
        where
            (kind, homogeneous) = case thmType of
                HidingThm -> (LinkKindHiding, True)
                FreeOrCofreeThm freeOrCofree -> case freeOrCofree of
                    Free -> (LinkKindFree, True)
                    Cofree -> (LinkKindCofree, True)
                GlobalOrLocalThm scope isHomogeneous -> case scope of
                    Global -> (LinkKindGlobal, isHomogeneous)
                    Local -> (LinkKindLocal, isHomogeneous)
    where
        inclusion = isInc . getRealDGLinkType $ l


referencedNodeLibName :: DGNodeLab -> LibName
referencedNodeLibName = dgn_libname

isNodeReferenceNode :: DGNodeLab -> Bool
isNodeReferenceNode = isDGRef


-- optsWithAnalysis :: HetcatsOpts -> AnaType -> HetcatsOpts
-- optsWithAnalysis o v = o {analysis = v}
optsWithUrlCatalog :: HetcatsOpts -> [(String, String)] -> HetcatsOpts
optsWithUrlCatalog o v = o {urlCatalog = v}
optsWithInfiles :: HetcatsOpts -> [FilePath]  -> HetcatsOpts
optsWithInfiles o v = o {infiles = v}
optsWithSpecNames :: HetcatsOpts -> [SIMPLE_ID] -> HetcatsOpts
optsWithSpecNames o v = o {specNames = v}
optsWithTransNames :: HetcatsOpts -> [SIMPLE_ID] -> HetcatsOpts
optsWithTransNames o v = o {transNames = v}
optsWithLossyTrans :: HetcatsOpts -> Bool                 -> HetcatsOpts
optsWithLossyTrans o v = o {lossyTrans = v}
optsWithViewNames :: HetcatsOpts -> [SIMPLE_ID] -> HetcatsOpts
optsWithViewNames o v = o {viewNames = v}
-- optsWithIntype :: HetcatsOpts -> InType -> HetcatsOpts
-- optsWithIntype o v = o {intype = v}
optsWithLibdirs :: HetcatsOpts -> [FilePath] -> HetcatsOpts
optsWithLibdirs o v = o {libdirs = v}
optsWithModelSparQ :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithModelSparQ o v = o {modelSparQ = v}
optsWithCounterSparQ :: HetcatsOpts -> Int -> HetcatsOpts
optsWithCounterSparQ o v = o {counterSparQ = v}
optsWithOutdir :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithOutdir o v = o {outdir = v}
-- optsWithOuttypes :: HetcatsOpts -> [OutType] -> HetcatsOpts
-- optsWithOuttypes o v = o {outtypes = v}
optsWithDatabaseDoMigrate :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithDatabaseDoMigrate o v = o {databaseDoMigrate = v}
optsWithDatabaseOutputFile :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithDatabaseOutputFile o v = o {databaseOutputFile = v}
optsWithDatabaseConfigFile :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithDatabaseConfigFile o v = o {databaseConfigFile = v}
optsWithDatabaseSubConfigKey :: HetcatsOpts -> String -> HetcatsOpts
optsWithDatabaseSubConfigKey o v = o {databaseSubConfigKey = v}
optsWithDatabaseFileVersionId :: HetcatsOpts -> String -> HetcatsOpts
optsWithDatabaseFileVersionId o v = o {databaseFileVersionId = v}
optsWithDatabaseReanalyze :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithDatabaseReanalyze o v = o {databaseReanalyze = v}
-- optsWithDatabaseConfig :: HetcatsOpts -> DBConfig.DBConfig -> HetcatsOpts
-- optsWithDatabaseConfig o v = o {databaseConfig = v}
-- optsWithDatabaseContext :: HetcatsOpts -> DBConfig.DBContext -> HetcatsOpts
-- optsWithDatabaseContext o v = o {databaseContext = v}
optsWithXupdate :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithXupdate o v = o {xupdate = v}
optsWithRecurse :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithRecurse o v = o {recurse = v}
optsWithVerbose :: HetcatsOpts -> Int -> HetcatsOpts
optsWithVerbose o v = o {verbose = v}
optsWithDefLogic :: HetcatsOpts -> String -> HetcatsOpts
optsWithDefLogic o v = o {defLogic = v}
optsWithDefSyntax :: HetcatsOpts -> String -> HetcatsOpts
optsWithDefSyntax o v = o {defSyntax = v}
optsWithOutputToStdout :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithOutputToStdout o v = o {outputToStdout = v}
-- optsWithCaslAmalg :: HetcatsOpts -> [CASLAmalgOpt] -> HetcatsOpts
-- optsWithCaslAmalg o v = o {caslAmalg = v}
optsWithInteractive :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithInteractive o v = o {interactive = v}
optsWithConnectP :: HetcatsOpts -> Int -> HetcatsOpts
optsWithConnectP o v = o {connectP = v}
optsWithConnectH :: HetcatsOpts -> String -> HetcatsOpts
optsWithConnectH o v = o {connectH = v}
optsWithUncolored :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithUncolored o v = o {uncolored = v}
optsWithXmlFlag :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithXmlFlag o v = o {xmlFlag = v}
optsWithApplyAutomatic :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithApplyAutomatic o v = o {applyAutomatic = v}
optsWithComputeNormalForm :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithComputeNormalForm o v = o {computeNormalForm = v}
optsWithDumpOpts :: HetcatsOpts -> [String] -> HetcatsOpts
optsWithDumpOpts o v = o {dumpOpts = v}
optsWithDisableCertificateVerification :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithDisableCertificateVerification o v = o {disableCertificateVerification = v}
-- optsWithIoEncoding :: HetcatsOpts -> Enc -> HetcatsOpts
-- optsWithIoEncoding o v = o {ioEncoding = v}
optsWithUseLibPos :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithUseLibPos o v = o {useLibPos = v}
optsWithUnlit :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithUnlit o v = o {unlit = v}
optsWithServe :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithServe o v = o {serve = v}
optsWithListen :: HetcatsOpts -> Int -> HetcatsOpts
optsWithListen o v = o {listen = v}
optsWithPidFile :: HetcatsOpts -> FilePath -> HetcatsOpts
optsWithPidFile o v = o {pidFile = v}
optsWithWhitelist :: HetcatsOpts -> [[String]] -> HetcatsOpts
optsWithWhitelist o v = o {whitelist = v}
optsWithBlacklist :: HetcatsOpts -> [[String]] -> HetcatsOpts
optsWithBlacklist o v = o {blacklist = v}
optsWithRunMMT :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithRunMMT o v = o {runMMT = v}
optsWithFullTheories :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithFullTheories o v = o {fullTheories = v}
optsWithOutputLogicList :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithOutputLogicList o v = o {outputLogicList = v}
optsWithOutputLogicGraph :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithOutputLogicGraph o v = o {outputLogicGraph = v}
optsWithFileType :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithFileType o v = o {fileType = v}
optsWithAccessToken :: HetcatsOpts -> String -> HetcatsOpts
optsWithAccessToken o v = o {accessToken = v}
optsWithHttpRequestHeaders :: HetcatsOpts -> [String] -> HetcatsOpts
optsWithHttpRequestHeaders o v = o {httpRequestHeaders = v}
optsWithFullSign :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithFullSign o v = o {fullSign = v}
optsWithPrintAST :: HetcatsOpts -> Bool -> HetcatsOpts
optsWithPrintAST o v = o {printAST = v}

