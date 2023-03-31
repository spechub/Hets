module HetsAPI.Internal (
    fromJust
    , Result, resultToMaybe, Diagnosis
    , HetcatsOpts, defaultHetcatsOpts
    , DGraph, DGNodeLab(dgn_name), DGLinkLab(dglName)
    , ProofStatus
    , GoalStatus
    , TimeOfDay
    , TacticScript
    , ProofState
    , ConsistencyStatus
    , sType
    , ConsStatus
    , requiredConservativity
    , provenConservativity
    , linkStatus
    , Conservativity
    , getNodeConsStatus
    , getConsOfStatus
    , isProvenConsStatusLink
    , showConsistencyStatus
) where


import Data.Maybe (fromJust)
import Data.Time (TimeOfDay)

import Common.Result (Result, resultToMaybe, Diagnosis)
import Common.Consistency(Conservativity(..), showConsistencyStatus)
import Driver.Options (HetcatsOpts, defaultHetcatsOpts)
import Static.DevGraph (DGraph, DGNodeLab(..), DGLinkLab(..), getNodeConsStatus, getNodeCons)
import Static.DgUtils (ConsStatus(..), getConsOfStatus, isProvenConsStatusLink)
import Logic.Prover (ProofStatus, GoalStatus, TacticScript)
import Proofs.AbstractState (ProofState)
import Proofs.ConsistencyCheck (ConsistencyStatus(..))
