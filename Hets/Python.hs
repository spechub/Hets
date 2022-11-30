module Hets.Python ( PyTheory
    -- Wrapped with PyTheory
    , getTheoryFromNode
    , usableProvers
    , autoProveNode

    -- Unchanged re-export from Hets.ProveCommands
    , proveNode
    , checkConsistency

    -- Unchanged re-export from Hets.Commands
    , automatic
    , globalSubsume
    , globalDecomposition
    , localInference
    , localDecomposition
    , compositionProveEdges
    , conservativity
    , automaticHideTheoremShift
    , theoremHideShift
    , computeColimit
    , normalForm
    , triangleCons
    , freeness
    , libFlatImports
    , libFlatDUnions
    , libFlatRenamings
    , libFlatHiding
    , libFlatHeterogen
    , qualifyLibEnv
    , loadLibrary
    , getGraphForLibrary
    , getNodesFromDevelopmentGraph
    , getLNodesFromDevelopmentGraph
)

where

import qualified Hets.Commands as HC
import qualified Hets.ProveCommands as HP

import qualified Static.GTheory as GT
import Static.DevGraph (DGNodeLab)
import Proofs.AbstractState (G_prover, ProofState, G_proof_tree)
import Logic.Comorphism (AnyComorphism)
import Common.ResultT (ResultT)
import Logic.Prover (ProofStatus)

-- TODO: Wrap all function calls that require existential datatypes like G_theory

data PyTheory = PyTheory GT.G_theory

getTheoryFromNode :: DGNodeLab -> PyTheory
getTheoryFromNode = PyTheory . dgn_theory

-- | @usableProvers theory@ checks for usable provers available on the machine
usableProvers :: PyTheory -> IO [(G_prover, AnyComorphism)]
usableProvers (PyTheory th) = HP.usableProvers th

-- | @proveNode theory prover comorphism@ proves all goals in @theory@ using all
--   all axioms in @theory@. If @prover@ or @comorphism@ is @Nothing@ the first
--   usable prover or comorphism is used. 
autoProveNode :: PyTheory -> Maybe G_prover -> Maybe AnyComorphism -> ResultT IO (ProofState, [ProofStatus G_proof_tree])
autoProveNode (PyTheory theory) = HP.autoProveNode theory