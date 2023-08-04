{- |
Description :  All commands to prove or check the consistency of a theory, node or edge
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.ProveCommands (
    getTheoryForSelection
    , getAvailableComorphisms
    , getUsableProvers
    , getUsableConsistencyCheckers

    , proveNode
    , recordProofResult
    , proveNodeAndRecord

    , checkConsistency
    , recordConsistencyResult
    , checkConsistencyAndRecord

    , checkConservativityNode

    , ProofOptions(..)
    , defaultProofOptions
    , ConsCheckingOptions(..)
    , defaultConsCheckingOptions
    , recomputeNode

    , genericProveBatch
) where

import HetsAPI.DataTypes

import Data.Functor ()
import qualified Data.Map as Map
import Data.Graph.Inductive (LNode, LEdge)

import Control.Monad.Trans ( MonadTrans(lift) )

import Common.Id (nullRange)
import Common.LibName (LibName)
import qualified Common.OrderedMap as OMap
import Common.Result (Result(maybeResult, Result), maybeToResult)
import Common.ResultT (ResultT, liftR)

import Comorphisms.LogicGraph (logicGraph)

import qualified Interfaces.Utils (checkConservativityNode, checkConservativityEdge)

import Logic.Comorphism (AnyComorphism)
import Logic.Grothendieck (findComorphismPaths)
import Logic.Prover (ProofStatus (goalName), ProverKind (..))

import Proofs.AbstractState (G_prover, ProofState, G_proof_tree, autoProofAtNode, G_cons_checker (..), getProverName, getConsCheckers, getCcName, makeTheoryForSentences)
import qualified Proofs.AbstractState as PAS
import Proofs.ConsistencyCheck (ConsistencyStatus, SType(..), consistencyCheck, sType)
import Proofs.BatchProcessing (genericProveBatch)

import Static.ComputeTheory(updateLabelTheory, recomputeNodeLabel)
import Static.DevGraph (LibEnv, DGraph, DGNodeLab, DGLinkLab, ProofHistory, DGChange(..), globalTheory, markNodeInconsistent, markNodeConsistent)
import Static.GTheory (G_theory (..), sublogicOfTh, coerceThSens)
import Static.History (changeDGH)
import Data.Maybe (fromJust)

data ProofOptions = ProofOptions {
    proofOptsProver :: Maybe G_prover -- ^ The prover to use. If not set, it is selected automatically
    , proofOptsComorphism :: Maybe AnyComorphism -- ^ The comorphism to use. If not set, it is selected automatically
    , proofOptsUseTheorems :: Bool -- ^ Indicates whether or not to use theorems is subsequent proofs
    , proofOptsGoalsToProve :: [String] -- ^ The names of the goals to prove. If empty, all goals are proven
    , proofOptsAxiomsToInclude :: [String] -- ^ The names of the axioms to include in the prove. If empty, all axioms are included
    , proofOptsTimeout :: Int -- ^ The timeout in seconds
}

defaultProofOptions :: ProofOptions
defaultProofOptions = ProofOptions {
    proofOptsProver = Nothing -- Automatically choose a prover
    , proofOptsComorphism = Nothing -- Autormatically select a comorphism
    , proofOptsUseTheorems = True
    , proofOptsGoalsToProve = [] -- Prove all goals
    , proofOptsAxiomsToInclude = [] -- Use all axioms
    , proofOptsTimeout = 600 -- Timeout 10min
}

data ConsCheckingOptions = ConsCheckingOptions {
    consOptsConsChecker :: Maybe G_cons_checker -- ^ The conschecker to use. If not set, it is selected automatically
    , consOptsComorphism :: Maybe AnyComorphism -- ^ The comorphism to use. If not set, it is selected automatically
    , consOptsIncludeTheorems :: Bool -- ^ Indicates whether or not to include theorems in the consistency check
    , consOptsTimeout :: Int -- ^ The timeout in seconds
}

defaultConsCheckingOptions :: ConsCheckingOptions
defaultConsCheckingOptions = ConsCheckingOptions {
    consOptsConsChecker = Nothing -- Automatically choose a cons checker
    , consOptsComorphism = Nothing -- Autormatically select a comorphism
    , consOptsIncludeTheorems = True
    , consOptsTimeout = 600 -- Timeout 10min
}

type ProofResult = (G_theory -- The new theory
    , [ProofStatus G_proof_tree]) -- ProofStatus of each goal


getTheoryForSelection :: [String] -> [String] -> [String] -> G_theory -> G_theory
getTheoryForSelection = makeTheoryForSentences

-- | @getAvailableComorphisms theory@ yields all available comorphisms for @theory@
getAvailableComorphisms :: G_theory -> [AnyComorphism]
getAvailableComorphisms = findComorphismPaths logicGraph . sublogicOfTh

-- | @getUsableConsistencyCheckers theory@ checks for usable consistencey checkers  
--   for @theory@ available on the machine
getUsableConsistencyCheckers :: G_theory -> IO [(G_cons_checker, AnyComorphism)]
getUsableConsistencyCheckers = getConsCheckers . getAvailableComorphisms

-- | @getUsableProvers theory@ checks for usable provers available on the machine
getUsableProvers :: G_theory -> IO [(G_prover, AnyComorphism)]
getUsableProvers th = PAS.getUsableProvers ProveCMDLautomatic (sublogicOfTh th) logicGraph

-- | @proveNode theory prover comorphism@ proves all goals in @theory@ using all
--   all axioms in @theory@. If @prover@ or @comorphism@ is @Nothing@ the first
--   usable prover or comorphism, respectively, is used. 
proveNode :: TheoryPointer -> ProofOptions -> ResultT IO ProofResult
proveNode (_, _, _, node) (ProofOptions proverM comorphismM useTh goals axioms timeout) = do
    theory <- liftR . maybeToResult nullRange "No global theory!" . globalTheory . snd $ node
    (prover, comorphism) <- case (proverM, comorphismM) of
        (Just prover, Just comorphism) -> return (prover, comorphism)
        (Just prover, Nothing) -> do
            let proverName = getProverName prover
            comorphism <- lift
                (snd . head . filter ((== proverName) . getProverName . fst) <$> getUsableProvers theory)
            return (prover, comorphism)
        (Nothing, Just comorphism) -> do
            prover <- lift
                (fst . head . filter ((== comorphism) . snd) <$> getUsableProvers theory)
            return (prover, comorphism)
        (Nothing, Nothing) -> head <$> lift (getUsableProvers theory)

    ((th, sens), (state, steps)) <- autoProofAtNode useTh timeout goals axioms theory (prover, comorphism)
    return (th, steps)

recordProofResult :: TheoryPointer -> ProofResult -> LibEnv
recordProofResult (name, env, graph, node) (theory, statuses) =
    if null statuses
    then env
    else case new_theory of
        Just th -> Map.insert name ( updateLabelTheory env name graph node th) env
        Nothing -> env
    where new_theory = do
            original_theory <- globalTheory . snd $ node
            recordProofResult' original_theory theory statuses

recordProofResult' :: G_theory -> G_theory -> [ProofStatus G_proof_tree] -> Maybe G_theory
recordProofResult' (G_theory lid1 _ _ _ original_sens _) (G_theory lid2 syn sign signIdx result_sens sensIdx) statuses = do
    original_sens' <- coerceThSens lid1 lid2 "String" original_sens
    let new_sens = foldr (\status sens -> OMap.insert (goalName status) (fromJust . OMap.lookup (goalName status) $ result_sens) sens) original_sens' statuses
    return $ G_theory lid2 syn sign signIdx new_sens sensIdx

proveNodeAndRecord :: TheoryPointer -> ProofOptions -> ResultT IO (ProofResult, LibEnv)
proveNodeAndRecord p@(_, _, _, node) opts = do
    r <- proveNode p opts
    let env = recordProofResult p r
    return (r, env)

checkConsistency :: TheoryPointer -> ConsCheckingOptions -> IO ConsistencyStatus
checkConsistency (libName, libEnv, dgraph, lnode) (ConsCheckingOptions ccM comorphismM b timeout)  = case globalTheory . snd $ lnode of
    Nothing -> fail "No global theory!"
    Just theory -> do
        (cc, comorphism) <- case (ccM, comorphismM) of
            (Just cc, Just comorphism) -> return (cc, comorphism)
            (Just cc, Nothing) -> do
                let ccName = getCcName cc
                comorphism <-  (snd . head . filter ((== ccName) . getCcName . fst) <$> getUsableConsistencyCheckers theory)
                return (cc, comorphism)
            (Nothing, Just comorphism) -> do
                cc <- (fst . head . filter ((== comorphism) . snd) <$> getUsableConsistencyCheckers theory)
                return (cc, comorphism)
            (Nothing, Nothing) -> head <$> (getUsableConsistencyCheckers theory)

        consistencyCheck b cc comorphism libName libEnv dgraph lnode timeout

recordConsistencyResult :: TheoryPointer -> ConsistencyStatus -> LibEnv
recordConsistencyResult (name, env, graph, node@(i, label)) consStatus =
    if sType consStatus == CSUnchecked
    then env
    else Map.insert name (changeDGH graph $ SetNodeLab label
                 (i, case sType consStatus of
                       CSInconsistent -> markNodeInconsistent "" label
                       CSConsistent -> markNodeConsistent "" label
                       _ -> label)) env

checkConsistencyAndRecord :: TheoryPointer -> ConsCheckingOptions -> IO (ConsistencyStatus, LibEnv)
checkConsistencyAndRecord p opts = do
    r <- checkConsistency p opts
    let env = recordConsistencyResult p r
    return (r, env)

checkConservativityNode ::LNode DGNodeLab -> LibEnv -> LibName
  -> IO (String, LibEnv, ProofHistory)
checkConservativityNode = Interfaces.Utils.checkConservativityNode False

checkConservativityEdge :: LEdge DGLinkLab -> LibEnv -> LibName 
    -> IO (String, LibEnv, LEdge DGLinkLab, ProofHistory)
checkConservativityEdge = Interfaces.Utils.checkConservativityEdge False

recomputeNode :: TheoryPointer -> LibEnv
recomputeNode (name, env, graph, node@(i, label)) =
    Map.insert name (changeDGH graph $ SetNodeLab label
        (i, recomputeNodeLabel env name graph node)) env
