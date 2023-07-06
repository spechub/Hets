{- |
Description :  This module aims to bundle all internals required to work with the API. The main reason is for the Python API to only import to modules.
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}

module HetsAPI.Internal (
    fromJust
    , Result, resultToMaybe, Diagnosis
    , HetcatsOpts, defaultHetcatsOpts
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
    , SType
    , ConsStatus
    , requiredConservativity
    , provenConservativity
    , linkStatus
    , Conservativity
    , getNodeConsStatus
    , getConsOfStatus
    , isProvenConsStatusLink
    , showConsistencyStatus
    , isInternalNode
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

    , LibName
    , LibEnv

    , IRI

    , showGlobalDoc
    , showDoc
) where


import Data.Maybe (fromJust)
import Data.Time (TimeOfDay)

import Common.DocUtils(showGlobalDoc, showDoc)
import Common.ExtSign (ExtSign(..))
import Common.Consistency(Conservativity(..), showConsistencyStatus)
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.LibName (LibName)
import Common.Result (Result, resultToMaybe, Diagnosis)
import Driver.Options (HetcatsOpts, defaultHetcatsOpts)
import Static.DevGraph (DGraph, DGNodeLab(..), DGLinkLab(..), getNodeConsStatus, getNodeCons, getDGNodeName, globalAnnos, LibEnv, isInternalNode, getRealDGLinkType)
import Static.DgUtils (ConsStatus(..), getConsOfStatus, isProvenConsStatusLink, NodeName, DGNodeType(..), DGEdgeType(..), DGEdgeTypeModInc(..), Scope(..), ThmTypes(..), FreeOrCofree(..), getEdgeNum)
import Logic.Prover (ProofStatus(..), GoalStatus(..), TacticScript(..))
import Proofs.AbstractState (ProofState)
import Proofs.ConsistencyCheck (ConsistencyStatus(..), SType)

developmentGraphNodeLabelName :: DGNodeLab -> String
developmentGraphNodeLabelName = getDGNodeName


developmentGraphEdgeLabelName :: DGLinkLab -> String
developmentGraphEdgeLabelName = dglName

developmentGraphEdgeLabelId :: DGLinkLab -> Int
developmentGraphEdgeLabelId = getEdgeNum . dgl_id


consistencyStatusType :: ConsistencyStatus -> SType
consistencyStatusType = sType

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









