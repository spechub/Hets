module HetsAPI.Python (
    PyTheory
    , PyComorphism
    , PyProver
    -- Wrapped with Py*
    , getTheoryFromNode
    , usableProvers
    , autoProveNode
    , translateTheory
    , availableComorphisms
    , usableConsistencyCheckers
    , checkConsistency
    , proveNode
    , getAllSentences
    , getAllAxioms
    , getAllGoals
    , getProvenGoals
    , getUnprovenGoals
    , getConsCheckerName
    , getComorphismName
    , getProverName

    -- Unchanged re-export from Hets.ProveCommands
    , HP.checkConservativityNode

    -- Unchanged re-export from Hets.Commands
    , HC.automatic
    , HC.globalSubsume
    , HC.globalDecomposition
    , HC.localInference
    , HC.localDecomposition
    , HC.compositionProveEdges
    , HC.conservativity
    , HC.automaticHideTheoremShift
    , HC.theoremHideShift
    , HC.computeColimit
    , HC.normalForm
    , HC.triangleCons
    , HC.freeness
    , HC.libFlatImports
    , HC.libFlatDUnions
    , HC.libFlatRenamings
    , HC.libFlatHiding
    , HC.libFlatHeterogen
    , HC.qualifyLibEnv
    , HC.loadLibrary
    , HC.showTheory
    , HI.getGraphForLibrary
    , HI.getNodesFromDevelopmentGraph
    , HI.getLNodesFromDevelopmentGraph
)

where

import Data.Functor

import qualified HetsAPI.Commands as HC
import qualified HetsAPI.ProveCommands as HP
import qualified HetsAPI.InfoCommands as HI

import Common.DocUtils (pretty)
import Common.ExtSign (plainSign)
import Common.LibName (LibName)
import Common.Result (Result)
import Common.ResultT (ResultT (runResultT))

import Data.Graph.Inductive (LNode)
import Data.Bifunctor (bimap)

import Logic.Comorphism (AnyComorphism)
import Logic.Logic (sym_of, PrintTypeConv)
import Logic.Prover (ProofStatus)
import Static.DevGraph (DGNodeLab (dgn_theory), LibEnv, DGraph)
import qualified Static.GTheory as GT
import Proofs.ConsistencyCheck (ConsistencyStatus)
import qualified Proofs.AbstractState
import Proofs.AbstractState (G_prover, ProofState, G_proof_tree, G_cons_checker)
import ATerm.AbstractSyntax (ATermTable)
import HetsAPI.DataTypes (SentenceByName)



-- Datatypes used for wrapping existential datatypes for an easier use in hyphen

data PyTheory = PyTheory GT.G_theory
data PyProver = PyProver G_prover
data PyConsChecker = PyConsChecker G_cons_checker
data PyComorphism = PyComorphism AnyComorphism
data PySentence = PySentence (ATermTable, Int)

instance Show PyTheory where
    show (PyTheory GT.G_theory { GT.gTheoryLogic = lid, GT.gTheorySign = extSign }) =
        "PyTheory "++ show (pretty <$> sym_of lid (plainSign extSign))

instance Show PyProver where
    show (PyProver p) = "PyProver "++ show p

instance Show PyComorphism where
    show (PyComorphism c) = "PyComorphism "++ show c

getProverName :: PyProver -> String
getProverName (PyProver p) = Proofs.AbstractState.getProverName p


getComorphismName :: PyComorphism -> String
getComorphismName (PyComorphism c) = show c

getConsCheckerName :: PyConsChecker -> String
getConsCheckerName (PyConsChecker cc) = Proofs.AbstractState.getCcName cc

getTheoryFromNode :: DGNodeLab -> PyTheory
getTheoryFromNode = PyTheory . dgn_theory

-- | @usableProvers theory@ checks for usable provers available on the machine
usableProvers :: PyTheory -> IO [(PyProver, PyComorphism)]
usableProvers (PyTheory th) = do
    provers <- HP.usableProvers th
    let toPy (p, c) = (PyProver p, PyComorphism c)
    return $ fmap toPy provers

-- | @proveNode theory prover comorphism@ proves all goals in @theory@ using all
--   all axioms in @theory@. If @prover@ or @comorphism@ is @Nothing@ the first
--   usable prover or comorphism is used. 
autoProveNode :: PyTheory -> Maybe PyProver -> Maybe PyComorphism -> IO (Result (PyTheory, ProofState, [ProofStatus G_proof_tree]))
autoProveNode (PyTheory theory) prover comorphism = runResultT $ (\(th, ps, tree) -> (PyTheory th, ps, tree)) <$>
    HP.autoProveNode theory ((\(PyProver p) -> p) <$> prover) ((\(PyComorphism c) -> c) <$> comorphism)

translateTheory :: PyComorphism -> PyTheory -> Result PyTheory
translateTheory (PyComorphism comorphism) (PyTheory theory) = HC.translateTheory comorphism theory <&> PyTheory

availableComorphisms :: PyTheory -> [PyComorphism]
availableComorphisms (PyTheory theory) = PyComorphism <$> HP.availableComorphisms theory

usableConsistencyCheckers :: PyTheory -> IO [(PyConsChecker, PyComorphism)]
usableConsistencyCheckers (PyTheory th) =
    fmap (bimap PyConsChecker PyComorphism) <$> HP.usableConsistencyCheckers th

checkConsistency :: Bool -> PyConsChecker -> PyComorphism -> LibName -> LibEnv
                 -> DGraph -> LNode DGNodeLab -> Int -> IO ConsistencyStatus
checkConsistency u (PyConsChecker cc) (PyComorphism c) = HP.checkConsistency u cc c


proveNode :: Bool -> Int -> [String] -> [String] -> PyTheory
    -> (PyProver, PyComorphism)
    -> ResultT IO (ProofState, [ProofStatus G_proof_tree])
proveNode sub timeout goals axioms
    (PyTheory theory)
    (PyProver prover, PyComorphism com) =
        HP.proveNode sub timeout goals axioms theory (prover, com)

getAllSentences :: PyTheory -> SentenceByName
getAllSentences (PyTheory theory) = HI.getAllSentences theory

getAllAxioms :: PyTheory -> SentenceByName
getAllAxioms (PyTheory theory) = HI.getAllAxioms theory

getAllGoals :: PyTheory -> SentenceByName
getAllGoals (PyTheory theory) = HI.getAllGoals theory

getProvenGoals :: PyTheory -> SentenceByName
getProvenGoals (PyTheory theory) = HI.getProvenGoals theory

getUnprovenGoals :: PyTheory -> SentenceByName
getUnprovenGoals (PyTheory theory) = HI.getUnprovenGoals theory
