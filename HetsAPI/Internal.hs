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
    , developmentGraphNodeLabelName
    , developmentGraphEdgeLabelName
    , ProofStatus
    , GoalStatus
    , TimeOfDay
    , TacticScript
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
    , getDGNodeName
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

    , IRI
) where


import Data.Maybe (fromJust)
import Data.Time (TimeOfDay)

import Common.ExtSign (ExtSign(..))
import Common.Consistency(Conservativity(..), showConsistencyStatus)
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.Result (Result, resultToMaybe, Diagnosis)
import Driver.Options (HetcatsOpts, defaultHetcatsOpts)
import Static.DevGraph (DGraph, DGNodeLab(..), DGLinkLab(..), getNodeConsStatus, getNodeCons, getDGNodeName, globalAnnos)
import Static.DgUtils (ConsStatus(..), getConsOfStatus, isProvenConsStatusLink, NodeName)
import Logic.Prover (ProofStatus, GoalStatus, TacticScript)
import Proofs.AbstractState (ProofState)
import Proofs.ConsistencyCheck (ConsistencyStatus(..), SType)

developmentGraphNodeLabelName :: DGNodeLab -> NodeName
developmentGraphNodeLabelName = dgn_name

developmentGraphEdgeLabelName :: DGLinkLab -> String
developmentGraphEdgeLabelName = dglName

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
