module Hets.ProveCommands (
    usableProvers
    , autoProveNode
    , proveNode
) where

import Data.Functor ()

import Control.Monad.Trans ( MonadTrans(lift) )

import Common.LibName (LibName)
import Common.ResultT (ResultT)

import Comorphisms.KnownProvers (knownProversWithKind)
import Comorphisms.LogicGraph (logicGraph)
import Logic.Comorphism (AnyComorphism)
import Logic.Prover (ProofStatus, ProverKind (..))
import Proofs.AbstractState (G_prover, ProofState, G_proof_tree, autoProofAtNode, getUsableProvers, G_cons_checker (..), getProverName, getConsCheckers)
import Static.DevGraph (LibEnv, DGraph, lookupDGraph, DGNodeLab, labNodesDG)
import Static.GTheory (G_theory (..), sublogicOfTh, proveSens)
import Data.Graph.Inductive (LNode)
-- | @usableProvers theory@ checks for usable provers available on the machine
usableProvers :: G_theory -> IO [(G_prover, AnyComorphism)]
usableProvers th = getUsableProvers ProveCMDLautomatic (sublogicOfTh th) logicGraph

-- | @proveNode theory prover comorphism@ proves all goals in @theory@ using all
--   all axioms in @theory@. If @prover@ or @comorphism@ is @Nothing@ the first
--   usable prover or comorphism is used. 
autoProveNode :: G_theory -> Maybe G_prover -> Maybe AnyComorphism -> ResultT IO (ProofState, [ProofStatus G_proof_tree])
autoProveNode theory proverM comorphismM = do
    (prover, comorphism) <- case (proverM, comorphismM) of
        (Just prover, Just comorphism) -> return (prover, comorphism)
        (Just prover, Nothing) -> do
            let proverName = getProverName prover
            comorphism <- lift
                (snd . head . filter ((== proverName) . getProverName . fst) <$> usableProvers theory)
            return (prover, comorphism)
        (Nothing, Just comorphism) -> do
            prover <- lift
                (fst . head . filter ((== comorphism) . snd) <$> usableProvers theory)
            return (prover, comorphism)
        (Nothing, Nothing) -> head <$> lift (usableProvers theory)

    snd <$> autoProofAtNode True 600 [] [] theory (prover, comorphism)

-- | @proveNode sub timeout goals axioms theory (prover, comorphism)@ proves
--   @goals@ with @prover@ after applying @comorphism@. If @goals@ is empty all
--   goals are selected. Same for @axioms@. If @sub@ is set theorems are used in
--   subsequent proofs. The runtime is restricted by @timeout@. 
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


