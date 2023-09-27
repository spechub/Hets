{-# LANGUAGE OverloadedStrings #-}
{- |
Description :  HetsAPIs python interface. This module reexports all commands and functionality from the API and hides certain unsupported features from the python interface.
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.Python (
    PyTheory
    , PyComorphism
    , PyProver
    , PyProofOptions(..)
    , PyProofTree
    , PyConsChecker
    , PyConservativityChecker
    , PyConsCheckingOptions(..)
    , PyGMorphism
    , PyBasicProof(..)
    , PyTheorySentence
    , PyTheorySentenceByName
    , mkPyProofOptions
    -- Wrapped with Py*

    , getTheoryForSelection
    , sublogicOfPyTheory
    , theoryOfNode
    , getUsableProvers
    , translateTheory
    , getAvailableComorphisms
    , getUsableConsistencyCheckers
    , getUsableConservativityCheckers
    , checkConsistency
    , checkConsistencyAndRecord
    , checkConservativityEdge
    , checkConservativityEdgeAndRecord
    , proveNode
    , recordProofResult
    , proveNodeAndRecord
    , getAllSentences
    , getAllAxioms
    , getAllGoals
    , getProvenGoals
    , getUnprovenGoals
    , consCheckerName
    , conservativityCheckerName
    , conservativityCheckerUsable
    , comorphismName
    , proverName
    , prettySentence
    , defaultProofOptions
    , defaultConsCheckingOptions
    , globalTheory
    , gmorphismOfEdge
    , comorphismOfGMorphism
    , signatureOfGMorphism
    , signatureOfTheory
    , pyProofStatusOfPyBasicProof

    , logicNameOfTheory
    , logicDescriptionOfTheory
    , targetLogicName
    , targetLogicDescriptionName
    , sourceLogicName
    , sourceLogicDescriptionName
    , comorphismNameOfGMorphism
    , comorphismDescriptionOfGMorphism
    , domainOfGMorphism
    , codomainOfGMorphism
    , isGMorphismInclusion
    , gMorphismToTransportType
    , theorySentenceBestProof

    -- Unchanged re-export from Hets.ProveCommands
    , HP.recomputeNode
    , HP.recordConservativityResult

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
    , HI.getEdgesFromDevelopmentGraph
    , HI.getLEdgesFromDevelopmentGraph
    , HI.getDevelopmentGraphNodeType
    , HI.theorySentenceIsAxiom
    , HI.theorySentenceWasTheorem
    , HI.theorySentenceIsDefined
    , HI.theorySentenceGetTheoremStatus
    , HI.theorySentencePriority
    , HI.theorySentenceContent
    , HI.getLibraryDependencies
    , HI.getRefinementTree
    , HI.getAvailableSpecificationsForRefinement

    , fstOf3
    , sndOf3
    , thd
    , getDGNodeById

    -- Datatypes
    , HDT.Sentence
    , HDT.TheorySentence
    , HDT.TheorySentenceByName
    , HDT.TheoryPointer
    , HDT.LinkPointer
    , HDT.SignatureJSON
    , HDT.SymbolJSON

    , Refinement.RefinementTreeNode(..)
    , Refinement.RefinementTreeLink(..)
    , Refinement.RefinementTreeLinkType(..)
)

where


import qualified HetsAPI.Commands as HC
import qualified HetsAPI.ProveCommands as HP
import qualified HetsAPI.InfoCommands as HI
import qualified HetsAPI.DataTypes as HDT
import HetsAPI.DataTypes (TheorySentence, Sentence)

import Common.AS_Annotation (SenAttr(..))
import Common.Consistency (Conservativity)
import Common.DocUtils (pretty)
import Common.ExtSign (ExtSign(..))
import Common.LibName (LibName)
import qualified Common.OrderedMap as OMap
import Common.Result (Result)
import Common.ResultT (ResultT (runResultT))

import Data.Aeson(encode, object, (.=))
import Data.Bifunctor (bimap)
import Data.Functor
import Data.Graph.Inductive (lab, LEdge)
import qualified Data.Set as Set

import Logic.Comorphism (AnyComorphism(..), targetLogic, sourceLogic)
import Logic.Grothendieck (GMorphism(..))
import Logic.Logic (sym_of, language_name, description, dom, cod, isInclusion)
import Logic.Prover (ProofStatus(..), ThmStatus(..))

import Static.DevGraph (DGNodeLab (dgn_theory), DGLinkLab(dgl_morphism), LibEnv, DGraph, dgBody)
import qualified Static.DevGraph (DGNodeLab(globalTheory))
import qualified Static.GTheory as GT
import Static.GTheory (BasicProof(..), sublogicOfTh)

import qualified Proofs.AbstractState
import Proofs.AbstractState (G_prover, G_proof_tree(..), G_cons_checker, G_conservativity_checker, conservativityCheckerId)
import Proofs.ConsistencyCheck (ConsistencyStatus)

import qualified HetsAPI.Refinement as Refinement


fstOf3 :: (a,b,c) -> a
fstOf3 (x, _, _) = x

sndOf3 :: (a,b,c) -> b
sndOf3 (_, x, _) = x

thd :: (a, b, c) -> c
thd (_, _, x) = x;

-- Datatypes used for wrapping existential datatypes for an easier use in hyphen

data PyTheory = PyTheory GT.G_theory
data PyProver = PyProver G_prover
data PyConsChecker = PyConsChecker G_cons_checker
data PyConservativityChecker = PyConservativityChecker G_conservativity_checker
data PyComorphism = PyComorphism AnyComorphism
data PyProofTree = PyProofTree G_proof_tree

toPyProofTree :: G_proof_tree -> PyProofTree
toPyProofTree = PyProofTree

fromPyProofTree :: PyProofTree -> G_proof_tree
fromPyProofTree (PyProofTree tree ) = tree

data PyGMorphism = PyGMorphism GMorphism
data PyBasicProof = PyBasicProof BasicProof
    | PyBasicProofGuessed
    | PyBasicProofConjectured
    | PyBasicProofHandwritten

instance Eq PyBasicProof where
    a == b = fromPyBasicProof a == fromPyBasicProof b

instance Ord PyBasicProof where
    compare a b = compare (fromPyBasicProof a) (fromPyBasicProof b)

fromPyBasicProof :: PyBasicProof -> BasicProof
fromPyBasicProof pb = case pb of
    PyBasicProof b -> b
    PyBasicProofGuessed -> Guessed
    PyBasicProofConjectured -> Conjectured
    PyBasicProofHandwritten -> Handwritten

toPyBasicProof :: BasicProof -> PyBasicProof
toPyBasicProof b = case b of
    BasicProof _ _ -> PyBasicProof b
    Guessed -> PyBasicProofGuessed
    Conjectured -> PyBasicProofConjectured
    Handwritten -> PyBasicProofHandwritten

type PyTheorySentence = SenAttr Sentence (ThmStatus (PyComorphism, PyBasicProof))
type PyTheorySentenceByName = OMap.OMap String PyTheorySentence

toPyTheorySentence :: TheorySentence -> PyTheorySentence
toPyTheorySentence sen = sen {senAttr = ThmStatus (fmap (bimap PyComorphism toPyBasicProof) $ getThmStatus . senAttr $ sen)}

pyProofStatusOfPyBasicProof :: PyBasicProof -> Maybe (ProofStatus PyProofTree)
pyProofStatusOfPyBasicProof b = case b of
    PyBasicProof (BasicProof lid status) -> Just . toPyProofStatus $ status {proofTree = G_proof_tree lid $ proofTree status }
    _ -> Nothing

data PyProofOptions = PyProofOptions {
    proofOptsProver :: Maybe PyProver -- ^ The prover to use. If not set, it is selected automatically
    , proofOptsComorphism :: Maybe PyComorphism -- ^ The comorphism to use. If not set, it is selected automatically
    , proofOptsUseTheorems :: Bool -- ^ Indicates whether or not to use theorems is subsequent proofs
    , proofOptsGoalsToProve :: [String] -- ^ The names of the goals to prove. If empty, all goals are proven
    , proofOptsAxiomsToInclude :: [String] -- ^ The names of the axioms to include in the prove. If empty, all axioms are included
    , proofOptsTimeout :: Int -- ^ The timeout in seconds
}
mkPyProofOptions :: Maybe PyProver -> Maybe PyComorphism -> Bool -> [String] -> [String] -> Int -> PyProofOptions
mkPyProofOptions = PyProofOptions

data PyConsCheckingOptions = PyConsCheckingOptions {
    consOptsConsChecker :: Maybe PyConsChecker -- ^ The conschecker to use. If not set, it is selected automatically
    , consOptsComorphism :: Maybe PyComorphism -- ^ The comorphism to use. If not set, it is selected automatically
    , consOptsIncludeTheorems :: Bool -- ^ Indicates whether or not to include theorems in the consistency check
    , consOptsTimeout :: Int -- ^ The timeout in seconds
}

toPyProofOptions :: HP.ProofOptions -> PyProofOptions
toPyProofOptions o = PyProofOptions {
    proofOptsProver = PyProver <$> HP.proofOptsProver o
    , proofOptsComorphism = PyComorphism <$> HP.proofOptsComorphism o
    , proofOptsUseTheorems = HP.proofOptsUseTheorems o
    , proofOptsGoalsToProve = HP.proofOptsGoalsToProve o
    , proofOptsAxiomsToInclude = HP.proofOptsAxiomsToInclude o
    , proofOptsTimeout = HP.proofOptsTimeout o
}

toProofOptions :: PyProofOptions -> HP.ProofOptions
toProofOptions o = HP.ProofOptions {
    HP.proofOptsProver = (\(PyProver p) -> p) <$> proofOptsProver o
    , HP.proofOptsComorphism = (\(PyComorphism c) -> c) <$> proofOptsComorphism o
    , HP.proofOptsUseTheorems = proofOptsUseTheorems o
    , HP.proofOptsGoalsToProve = proofOptsGoalsToProve o
    , HP.proofOptsAxiomsToInclude = proofOptsAxiomsToInclude o
    , HP.proofOptsTimeout = proofOptsTimeout o
}

toPyConsCheckingOptions :: HP.ConsCheckingOptions -> PyConsCheckingOptions
toPyConsCheckingOptions o = PyConsCheckingOptions {
    consOptsConsChecker = PyConsChecker <$> HP.consOptsConsChecker o
    , consOptsComorphism = PyComorphism <$> HP.consOptsComorphism o
    , consOptsIncludeTheorems = HP.consOptsIncludeTheorems o
    , consOptsTimeout = HP.consOptsTimeout o
}

toConsCheckingOptions :: PyConsCheckingOptions -> HP.ConsCheckingOptions
toConsCheckingOptions o = HP.ConsCheckingOptions {
    HP.consOptsConsChecker = (\(PyConsChecker c) -> c) <$> consOptsConsChecker o
    , HP.consOptsComorphism = (\(PyComorphism c) -> c) <$> consOptsComorphism o
    , HP.consOptsIncludeTheorems = consOptsIncludeTheorems o
    , HP.consOptsTimeout = consOptsTimeout o
}

defaultProofOptions :: PyProofOptions
defaultProofOptions = toPyProofOptions HP.defaultProofOptions

defaultConsCheckingOptions :: PyConsCheckingOptions
defaultConsCheckingOptions = toPyConsCheckingOptions HP.defaultConsCheckingOptions

instance Show PyTheory where
    show (PyTheory GT.G_theory { GT.gTheoryLogic = lid, GT.gTheorySign = extSign }) =
        "PyTheory "++ show (pretty <$> sym_of lid (plainSign extSign))

instance Show PyProver where
    show (PyProver p) = "PyProver "++ show p

instance Show PyComorphism where
    show (PyComorphism c) = "PyComorphism "++ show c

instance Show PyProofTree where
    show (PyProofTree t) = show t

proverName :: PyProver -> String
proverName (PyProver p) = Proofs.AbstractState.getProverName p

comorphismName :: PyComorphism -> String
comorphismName (PyComorphism c) = show c

targetLogicName :: PyComorphism -> String
targetLogicName (PyComorphism (Comorphism cid)) = language_name $ targetLogic cid

targetLogicDescriptionName :: PyComorphism -> String
targetLogicDescriptionName (PyComorphism (Comorphism cid)) = description $ targetLogic cid

sourceLogicName :: PyComorphism -> String
sourceLogicName (PyComorphism (Comorphism cid)) = language_name $ sourceLogic cid

sourceLogicDescriptionName :: PyComorphism -> String
sourceLogicDescriptionName (PyComorphism (Comorphism cid)) = description $ sourceLogic cid

consCheckerName :: PyConsChecker -> String
consCheckerName (PyConsChecker cc) = Proofs.AbstractState.getCcName cc

conservativityCheckerName :: PyConservativityChecker -> String
conservativityCheckerName (PyConservativityChecker cc) = conservativityCheckerId cc

conservativityCheckerUsable :: PyConservativityChecker -> IO (Maybe String)
conservativityCheckerUsable (PyConservativityChecker cc) = Proofs.AbstractState.conservativityCheckerUsable cc

theoryOfNode :: DGNodeLab -> PyTheory
theoryOfNode = PyTheory . dgn_theory

sublogicOfPyTheory :: PyTheory -> String
sublogicOfPyTheory (PyTheory th) = show . sublogicOfTh $ th

getTheoryForSelection :: [String] -> [String] -> [String] -> PyTheory -> PyTheory
getTheoryForSelection axioms goals theorems (PyTheory th) = PyTheory (HP.getTheoryForSelection axioms goals theorems th)

-- | @getUsableProvers theory@ checks for usable provers available on the machine
getUsableProvers :: PyTheory -> IO [(PyProver, PyComorphism)]
getUsableProvers (PyTheory th) = do
    provers <- HP.getUsableProvers th
    let toPy (p, c) = (PyProver p, PyComorphism c)
    return $ fmap toPy provers

toPyProofStatus :: ProofStatus G_proof_tree -> ProofStatus PyProofTree
toPyProofStatus status = status { proofTree = toPyProofTree (proofTree status) }

fromPyProofStatus :: ProofStatus PyProofTree -> ProofStatus G_proof_tree
fromPyProofStatus status  = status {proofTree = fromPyProofTree (proofTree status)}

proveNode :: HDT.TheoryPointer -> PyProofOptions -> IO (Result (PyTheory, [ProofStatus PyProofTree]))
proveNode ptr opts =
    runResultT $ bimap PyTheory (toPyProofStatus <$>) <$> HP.proveNode ptr (toProofOptions opts)

recordProofResult :: HDT.TheoryPointer -> (PyTheory, [ProofStatus PyProofTree]) -> LibEnv
recordProofResult ptr (PyTheory theory, statuses) = HP.recordProofResult ptr (theory, fmap fromPyProofStatus statuses)

proveNodeAndRecord :: HDT.TheoryPointer -> PyProofOptions -> IO (Result ((PyTheory, [ProofStatus PyProofTree]), LibEnv))
proveNodeAndRecord ptr opts =
    runResultT $ (\((th, trees), env) -> ((PyTheory th, toPyProofStatus <$> trees), env)) <$>
        HP.proveNodeAndRecord ptr (toProofOptions opts)

translateTheory :: PyComorphism -> PyTheory -> Result PyTheory
translateTheory (PyComorphism comorphism) (PyTheory theory) = HC.translateTheory comorphism theory <&> PyTheory

getAvailableComorphisms :: PyTheory -> [PyComorphism]
getAvailableComorphisms (PyTheory theory) = PyComorphism <$> HP.getAvailableComorphisms theory

getUsableConsistencyCheckers :: PyTheory -> IO [(PyConsChecker, PyComorphism)]
getUsableConsistencyCheckers (PyTheory th) =
    fmap (bimap PyConsChecker PyComorphism) <$> HP.getUsableConsistencyCheckers th

checkConsistency :: HDT.TheoryPointer -> PyConsCheckingOptions -> IO ConsistencyStatus
checkConsistency ptr = HP.checkConsistency ptr . toConsCheckingOptions

checkConsistencyAndRecord :: HDT.TheoryPointer -> PyConsCheckingOptions -> IO (ConsistencyStatus, LibEnv)
checkConsistencyAndRecord ptr = HP.checkConsistencyAndRecord ptr . toConsCheckingOptions

getUsableConservativityCheckers :: LEdge DGLinkLab -> LibEnv -> LibName -> IO [PyConservativityChecker]
getUsableConservativityCheckers edge env = fmap (fmap PyConservativityChecker) . HP.getUsableConservativityCheckers edge env

checkConservativityEdge :: PyConservativityChecker -> HDT.LinkPointer
  -> IO (Result (Conservativity, PyTheory, PyTheory))
checkConservativityEdge (PyConservativityChecker cc) linkPtr = do
    res <- HP.checkConservativityEdge linkPtr cc
    return $ do
        (consv, expl, obl) <- res
        return (consv, PyTheory expl, PyTheory obl)

checkConservativityEdgeAndRecord :: PyConservativityChecker -> HDT.LinkPointer
  -> IO (Result ((Conservativity, PyTheory, PyTheory), LibEnv))
checkConservativityEdgeAndRecord (PyConservativityChecker cc) linkPtr = do
    res <- HP.checkConservativityEdgeAndRecord linkPtr cc
    return $ do
        ((consv, expl, obl), env) <- res
        return ((consv, PyTheory expl, PyTheory obl), env)


getAllSentences :: PyTheory -> PyTheorySentenceByName
getAllSentences (PyTheory theory) = OMap.map toPyTheorySentence $ HI.getAllSentences theory

getAllAxioms :: PyTheory -> PyTheorySentenceByName
getAllAxioms (PyTheory theory) = OMap.map toPyTheorySentence $ HI.getAllAxioms theory

getAllGoals :: PyTheory -> PyTheorySentenceByName
getAllGoals (PyTheory theory) = OMap.map toPyTheorySentence $ HI.getAllGoals theory

getProvenGoals :: PyTheory -> PyTheorySentenceByName
getProvenGoals (PyTheory theory) = OMap.map toPyTheorySentence $ HI.getProvenGoals theory

getUnprovenGoals :: PyTheory -> PyTheorySentenceByName
getUnprovenGoals (PyTheory theory) = OMap.map toPyTheorySentence $ HI.getUnprovenGoals theory

theorySentenceBestProof :: PyTheorySentence -> Maybe PyBasicProof
theorySentenceBestProof = HI.theorySentenceBestProof

prettySentence :: PyTheory -> Sentence -> String
prettySentence (PyTheory theory) = HI.prettySentenceOfTheory theory

signatureOfTheory :: PyTheory -> ExtSign HDT.SignatureJSON HDT.SymbolJSON
signatureOfTheory (PyTheory GT.G_theory { GT.gTheorySign = sig }) = ExtSign {
        plainSign = encode (plainSign sig),
        nonImportedSymbols = Set.map encode $ nonImportedSymbols sig
    }

logicNameOfTheory :: PyTheory -> String
logicNameOfTheory (PyTheory GT.G_theory { GT.gTheoryLogic = lid } ) = language_name lid

logicDescriptionOfTheory :: PyTheory -> String
logicDescriptionOfTheory (PyTheory GT.G_theory { GT.gTheoryLogic = lid } ) = description lid

getDGNodeById :: DGraph -> Int -> Maybe DGNodeLab
getDGNodeById = lab . dgBody

globalTheory :: DGNodeLab -> Maybe PyTheory
globalTheory = fmap PyTheory . Static.DevGraph.globalTheory

gmorphismOfEdge :: DGLinkLab -> PyGMorphism
gmorphismOfEdge = PyGMorphism . Static.DevGraph.dgl_morphism

{-------------------------------------------------------------------------------
GMorphism Wrapper
-------------------------------------------------------------------------------}
comorphismOfGMorphism :: PyGMorphism -> PyComorphism
comorphismOfGMorphism (PyGMorphism GMorphism {gMorphismComor = cid}) = PyComorphism (Comorphism cid)

signatureOfGMorphism :: PyGMorphism -> ExtSign HDT.SignatureJSON HDT.SymbolJSON
signatureOfGMorphism (PyGMorphism GMorphism {gMorphismSign = sig}) = ExtSign {
        plainSign = encode (plainSign sig),
        nonImportedSymbols = Set.map encode $ nonImportedSymbols sig
    }

comorphismNameOfGMorphism :: PyGMorphism -> String
comorphismNameOfGMorphism (PyGMorphism GMorphism {gMorphismComor = cid}) = language_name cid

comorphismDescriptionOfGMorphism :: PyGMorphism -> String
comorphismDescriptionOfGMorphism (PyGMorphism GMorphism {gMorphismComor = cid}) = description cid

domainOfGMorphism :: PyGMorphism -> HDT.GenericTransportType
domainOfGMorphism (PyGMorphism GMorphism {gMorphismMor = m}) = encode $ dom m

codomainOfGMorphism :: PyGMorphism -> HDT.GenericTransportType
codomainOfGMorphism (PyGMorphism GMorphism {gMorphismMor = m}) = encode $ cod m

isGMorphismInclusion :: PyGMorphism -> Bool
isGMorphismInclusion (PyGMorphism m) = isInclusion m


gMorphismToTransportType :: PyGMorphism -> HDT.GenericTransportType
gMorphismToTransportType (PyGMorphism GMorphism {gMorphismComor = cid, gMorphismSign = sig, gMorphismMor = mor}) =
    encode $ object ["nameOfComorphism" .= show cid, "signature" .= sig, "morphism" .= mor]

-- symbolMapOfGMorphism :: PyGMorphism -> Map.Map HDT.SymbolJSON HDT.SymbolJSON
-- symbolMapOfGMorphism (PyGMorphism (GMorphism {gMorphismMor = morphism})) = Map.map encode $ Map.mapKeys encode $ symmap_of (targetLogic morphism) morphism

