import hyphen

hyphen.importing.FORCED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]
hyphen.importing.EXPECTED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]

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
from hs.Prelude import Just, Nothing, fst, snd, show, String

from hs.HetsAPI.Internal import (fromJust, Result, resultToMaybe, Diagnosis, HetcatsOpts, defaultHetcatsOpts, DGraph,
                                 DGNodeLab, ProofStatus, ProofState, ConsistencyStatus)

import hs.Common.OrderedMap as OMap

