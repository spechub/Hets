module Hets.ProveCommands (
    availableComorphisms
    , usableProvers
    , usableConsistencyCheckers
    , autoProveNode
    , proveNode
    , checkConsistency
    , checkConservativityNode
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
import Static.DevGraph (LibEnv, DGraph, lookupDGraph, DGNodeLab, labNodesDG, ProofHistory)
import Static.GTheory (G_theory (..), sublogicOfTh, proveSens)
import Data.Graph.Inductive (LNode)
import Proofs.ConsistencyCheck (ConsistencyStatus, consistencyCheck)
import Logic.Logic (Logic(cons_checkers))
import qualified Interfaces.Utils (checkConservativityNode)
import Logic.Grothendieck (findComorphismPaths)

-- | @availableComorphisms theory@ yields all available comorphisms for @theory@
availableComorphisms :: G_theory -> [AnyComorphism]
availableComorphisms = findComorphismPaths logicGraph . sublogicOfTh

-- | @usableConsistencyCheckers theory@ checks for usable consistencey checkers  
--   for @theory@ available on the machine
usableConsistencyCheckers :: G_theory -> IO [(G_cons_checker, AnyComorphism)]
usableConsistencyCheckers = getConsCheckers . availableComorphisms

-- | @usableProvers theory@ checks for usable provers available on the machine
usableProvers :: G_theory -> IO [(G_prover, AnyComorphism)]
usableProvers th = getUsableProvers ProveCMDLautomatic (sublogicOfTh th) logicGraph

-- | @proveNode theory prover comorphism@ proves all goals in @theory@ using all
--   all axioms in @theory@. If @prover@ or @comorphism@ is @Nothing@ the first
--   usable prover or comorphism, respectively, is used. 
autoProveNode :: G_theory -> Maybe G_prover -> Maybe AnyComorphism -> ResultT IO (G_theory, ProofState, [ProofStatus G_proof_tree])
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

    ((th, out), (state, steps)) <- autoProofAtNode True 600 [] [] theory (prover, comorphism)
    return (th, state, steps)

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

-- | @checkConsistency includeTheorems cc comorphism libname libenv 
--   dg node timeout@ first applies the comorphism @cc@ to the theory at @node@
--   in the developmentGraph @dg@ inside the library @libname@ in the environment
--   @libenv@, then checks the consistency using the consistency checker @cc@ 
--   with a timeout of @timeout@ seconds.
checkConsistency :: Bool -> G_cons_checker -> AnyComorphism -> LibName -> LibEnv
                 -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus
checkConsistency = consistencyCheck


checkConservativityNode ::LNode DGNodeLab -> LibEnv -> LibName
  -> IO (String, LibEnv, ProofHistory)
checkConservativityNode = Interfaces.Utils.checkConservativityNode False