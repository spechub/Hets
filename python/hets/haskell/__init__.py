import hyphen

hyphen.importing.EXPECTED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs"]

from hs.HetsAPI.Python import (PyTheory, PyComorphism, PyConsChecker, PyProver, autoProveNode, availableComorphisms,
                               getLNodesFromDevelopmentGraph, getTheoryFromNode, Sentence, SentenceByName,
                               usableConsistencyCheckers, usableProvers, thd, fstOf3, sndOf3,
                               getAllSentences, getAllAxioms, getAllGoals, prettySentence, checkConsistency,
                               getProvenGoals, getUnprovenGoals, getProverName, autoCheckConsistency,
                               getComorphismName, getConsCheckerName, loadLibrary, getGraphForLibrary, automatic,
                               globalSubsume, globalDecomposition, localInference, localDecomposition,
                               compositionProveEdges, conservativity, automaticHideTheoremShift, theoremHideShift,
                               computeColimit, normalForm, triangleCons, freeness, libFlatImports, libFlatDUnions,
                               libFlatRenamings, libFlatHiding, libFlatHeterogen, qualifyLibEnv)
from hs.Prelude import Just, Nothing, fst, snd, show

from hs.Data.Maybe import fromJust
from hs.Common.Result import Result, resultToMaybe, Diagnosis
import hs.Common.OrderedMap as OMap
from hs.Driver.Options import HetcatsOpts, defaultHetcatsOpts
from hs.Static.DevGraph import DGraph, DGNodeLab
from hs.Logic.Prover import ProofStatus
from hs.Proofs.AbstractState import ProofState
from hs.Proofs.ConsistencyCheck import ConsistencyStatus

