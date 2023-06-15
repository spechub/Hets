"""
Description :  Represents `Static.GTheory.G_theory`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import List, Optional, Tuple

from .HsWrapper import HsHierarchyElement
from .Logic import Logic
from .Signature import Signature
from .haskell import (Just, Nothing, fst, thd, PyTheory, getUsableProvers, getUsableConsistencyCheckers,
                      proveNodeAndRecord,
                      getAvailableComorphisms, getAllSentences, getAllGoals, getAllAxioms, getProvenGoals,
                      prettySentence,
                      getUnprovenGoals, OMap, fstOf3, sndOf3, ProofStatus, PyProver, PyComorphism, PyConsChecker,
                      ConsistencyStatus, defaultProofOptions, PyProofOptions, mkPyProofOptions, TheoryPointer, snd,
                      defaultConsCheckingOptions, PyConsCheckingOptions, checkConsistencyAndRecord, logicNameOfTheory,
                      logicDescriptionOfTheory, signatureOfTheory)

from .result import result_or_raise

from .Prover import Prover
from .ConsistencyChecker import ConsistencyChecker
from .Comorphism import Comorphism
from .ProofState import ProofState
from .Sentence import Sentence


class Theory(HsHierarchyElement):
    def __init__(self, hs_theory: PyTheory, parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)
        self._hs_theory = hs_theory
        self._hs_pretty_sentence = prettySentence(hs_theory)

    def hs_obj(self):
        return self._hs_theory

    def hs_update(self, new_hs_obj):
        self._hs_theory = new_hs_obj

    def get_usable_provers(self) -> List[Prover]:
        provers = getUsableProvers(self._hs_theory).act()
        return list({Prover(fst(p)) for p in provers})

    def get_prover_by_name(self, name: str) -> Optional[Prover]:
        matches = list(p for p in self.get_usable_provers() if p.name() == name)
        if len(matches) == 1:
            return matches[0]
        return None

    def get_usable_consistency_checkers(self) -> List[ConsistencyChecker]:
        ccs = getUsableConsistencyCheckers(self._hs_theory).act()
        return list({ConsistencyChecker(fst(cc)) for cc in ccs})

    def get_available_comorphisms(self) -> List[Comorphism]:
        comorphisms = getAvailableComorphisms(self._hs_theory)
        return [Comorphism(x) for x in comorphisms]

    def sentences(self) -> List[Sentence]:
        sentences = getAllSentences(self._hs_theory)
        return [Sentence(x, self._hs_pretty_sentence) for x in OMap.toList(sentences)]

    def axioms(self) -> List[Sentence]:
        axioms = getAllAxioms(self._hs_theory)
        return [Sentence(x, self._hs_pretty_sentence) for x in OMap.toList(axioms)]

    def goals(self) -> List[Sentence]:
        return [Sentence(x, self._hs_pretty_sentence) for x in OMap.toList(getAllGoals(self._hs_theory))]

    def proven_goals(self) -> List[Sentence]:
        return [Sentence(x, self._hs_pretty_sentence) for x in OMap.toList(getProvenGoals(self._hs_theory))]

    def unproven_goals(self) -> List[Sentence]:
        return [Sentence(x, self._hs_pretty_sentence) for x in OMap.toList(getUnprovenGoals(self._hs_theory))]

    def logic(self) -> Logic:
        return Logic(logicNameOfTheory(self._hs_theory), logicDescriptionOfTheory(self._hs_theory))

    def signature(self) -> Signature:
        return Signature(signatureOfTheory(self._hs_theory))

