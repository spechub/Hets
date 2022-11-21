module Hets.ProveCommand where

import Logic.Comorphism (AnyComorphism)
import Proofs.AbstractState (G_prover, ProofState, G_proof_tree, autoProofAtNode, getUsableProvers)
import Static.DevGraph (LibEnv, DGraph, lookupDGraph, DGNodeLab, labNodesDG)
import Static.GTheory (G_theory, sublogicOfTh, proveSens)
import Common.ResultT (ResultT)
import Logic.Prover (ProofStatus, ProverKind (..))
import Comorphisms.KnownProvers (knownProversWithKind)
import Comorphisms.LogicGraph (logicGraph)
import Common.LibName (LibName)

-- | @getDevelopmentGraphByName name env@ returns the development graph for the
--   library @name@ in the environment @env@.
getDevelopmentGraphByName :: LibName -> LibEnv -> DGraph
getDevelopmentGraphByName = lookupDGraph

-- | @getNodesFromDevelopmentGraph graph@ returns the nodes of the development
--   graph @graph@
getNodesFromDevelopmentGraph :: DGraph -> [DGNodeLab]
getNodesFromDevelopmentGraph = fmap snd . labNodesDG

-- | @usableProvers theory@ checks for usable provers available on the machine
usableProvers :: G_theory -> IO [(G_prover, AnyComorphism)]
usableProvers th = getUsableProvers ProveCMDLautomatic (sublogicOfTh th) logicGraph

-- | @proveNode sub timeout goals axioms theory (prover, comorphism)@ proves
--   @goals@ with @prover@ after applying @comorphism@. If @sub@ is set theorems
--   are used in subsequent proofs. The runtime is restricted by @timeout@. 
proveNode ::
    -- Use theorems is subsequent proofs
    Bool
    -- Timeout limit
    -> Int
    -- Goals to prove
    -> [String]
    -- Axioms useable for the prove
    -> [String]
    -- Theory
    -> G_theory
    -- Combination of prover and comorphism 
    -> (G_prover, AnyComorphism)
    -- returns new GoalStatus for the Node
    -> ResultT IO (ProofState, [ProofStatus G_proof_tree])
proveNode sub timeout goals axioms theory pc = snd <$>
    autoProofAtNode sub timeout goals axioms theory pc