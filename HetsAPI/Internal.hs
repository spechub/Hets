module HetsAPI.Internal (
    fromJust
    , Result, resultToMaybe, Diagnosis
    , HetcatsOpts, defaultHetcatsOpts
    , DGraph, DGNodeLab
    , ProofStatus
    , ProofState
    , ConsistencyStatus
) where


import Data.Maybe (fromJust)
import Common.Result (Result, resultToMaybe, Diagnosis)
import Driver.Options (HetcatsOpts, defaultHetcatsOpts)
import Static.DevGraph (DGraph, DGNodeLab)
import Logic.Prover (ProofStatus)
import Proofs.AbstractState (ProofState)
import Proofs.ConsistencyCheck (ConsistencyStatus)
