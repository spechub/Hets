"""
Description :  Python interface to the haskell API. Imports all functionality through hyphen.
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

import hyphen

# Some moules in a module hierarchy do not exist in haskell. E.g. the module `Driver.Options` in python implies the existence of a module `Driver` which does not have to exist in python. Hence, these modules need to be marked explicitly empty
hyphen.importing.FORCED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]
hyphen.importing.EXPECTED_EMPTY += ["Driver", "Common", "Static", "Logic", "Proofs", "HetsAPI"]

from hs.HetsAPI.Python import (PyTheory, PyComorphism, PyConsChecker, PyProver, PyProofOptions, PyConsCheckingOptions,
                               proveNodeAndRecord, getAvailableComorphisms, getLNodesFromDevelopmentGraph,
                               getLEdgesFromDevelopmentGraph, getEdgesFromDevelopmentGraph, theoryOfNode, Sentence,
                               SentenceByName, getUsableConsistencyCheckers, getUsableProvers, thd, fstOf3, sndOf3,
                               getAllSentences, getAllAxioms, getAllGoals, prettySentence, checkConsistencyAndRecord,
                               getProvenGoals, getUnprovenGoals, proverName, checkConsistency, comorphismName,
                               consCheckerName, loadLibrary, getGraphForLibrary, automatic, globalSubsume,
                               globalDecomposition, localInference, localDecomposition, compositionProveEdges,
                               conservativity, automaticHideTheoremShift, theoremHideShift, computeColimit, normalForm,
                               triangleCons, freeness, libFlatImports, libFlatDUnions, libFlatRenamings, libFlatHiding,
                               libFlatHeterogen, qualifyLibEnv, defaultProofOptions, defaultConsCheckingOptions,
                               TheoryPointer, mkPyProofOptions, getDGNodeById, recomputeNode, globalTheory,
                               gmorphismOfEdge, comorphismOfGMorphism, signatureOfGMorphism, PyGMorphism,
                               logicNameOfTheory, logicDescriptionOfTheory, targetLogicName, targetLogicDescriptionName,
                               sourceLogicName, sourceLogicDescriptionName, logicNameOfGMorphism,
                               logicDescriptionOfGMorphism)
from hs.Prelude import Just, Nothing, fst, snd, show, String

from hs.HetsAPI.Internal import (fromJust, Result, resultToMaybe, Diagnosis, HetcatsOpts, defaultHetcatsOpts, DGraph,
                                 DGNodeLab, DGLinkLab, ProofStatus, ProofState, ConsistencyStatus,
                                 ConsistencyStatus, ConsStatus, Conservativity, getNodeConsStatus,
                                 showConsistencyStatus, GoalStatus, TimeOfDay, TacticScript, getConsOfStatus,
                                 requiredConservativity, provenConservativity, linkStatus, plainSign,
                                 nonImportedSymbols, ExtSign, developmentGraphEdgeLabelName,
                                 developmentGraphNodeLabelName)

import hs.Common.OrderedMap as OMap
