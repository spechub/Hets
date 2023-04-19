"""
Description :  Represents `Static.GTheory.G_theory`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import List, Optional, Tuple

from .HsWrapper import HsHierarchyElement
from .haskell import (Just, Nothing, fst, thd, PyTheory, usableProvers, usableConsistencyCheckers, proveNodeAndRecord,
                      availableComorphisms, getAllSentences, getAllGoals, getAllAxioms, getProvenGoals, prettySentence,
                      getUnprovenGoals, OMap, fstOf3, sndOf3, ProofStatus, PyProver, PyComorphism, PyConsChecker,
                      ConsistencyStatus, defaultProofOptions, PyProofOptions, mkPyProofOptions, TheoryPointer, snd,
                      defaultConsCheckingOptions, PyConsCheckingOptions, checkConsistencyAndRecord)

from .result import resultOrRaise

from .Prover import Prover
from .ConsistencyChecker import ConsistencyChecker
from .Comorphism import Comorphism
from .ProofState import ProofState
from .Sentence import Sentence


class Theory(HsHierarchyElement):
    def __init__(self, hsTheory: PyTheory, parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)
        self._hsTheory = hsTheory
        self._hsPrettySentence = prettySentence(hsTheory)

    def hsObj(self):
        return self._hsTheory

    def hsUpdate(self, newHsObj):
        self._hsTheory = newHsObj

    def usableProvers(self) -> List[Prover]:
        provers = usableProvers(self._hsTheory).act()
        return list({Prover(fst(p)) for p in provers})

    def usableConsistencyCheckers(self) -> List[ConsistencyChecker]:
        ccs = usableConsistencyCheckers(self._hsTheory).act()
        return list({ConsistencyChecker(fst(cc)) for cc in ccs})

    def availableComorphisms(self) -> List[Comorphism]:
        comorphisms = availableComorphisms(self._hsTheory)
        return [Comorphism(x) for x in comorphisms]

    def sentences(self) -> List[Sentence]:
        sentences = getAllSentences(self._hsTheory)
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(sentences)]

    def axioms(self) -> List[Sentence]:
        axioms = getAllAxioms(self._hsTheory)
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(axioms)]

    def goals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getAllGoals(self._hsTheory))]

    def provenGoals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getProvenGoals(self._hsTheory))]

    def unprovenGoals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getUnprovenGoals(self._hsTheory))]
