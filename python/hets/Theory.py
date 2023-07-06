"""
Description :  Represents `Static.GTheory.G_theory`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import List, Optional, Tuple, Dict

from .Comorphism import Comorphism
from .ConsistencyChecker import ConsistencyChecker
from .HsWrapper import HsHierarchyElement
from .Logic import Logic
from .Prover import Prover
from .Sentence import Sentence
from .Signature import Signature
from .haskell import (fst, PyTheory, getUsableProvers, getUsableConsistencyCheckers,
                      getAvailableComorphisms, getAllSentences, getAllGoals, getAllAxioms, getProvenGoals,
                      prettySentence,
                      getUnprovenGoals, OMap, snd,
                      logicNameOfTheory,
                      logicDescriptionOfTheory, signatureOfTheory)


class Theory(HsHierarchyElement):
    def __init__(self, hs_theory: PyTheory, parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)
        self._sentences: Optional[List[Sentence]] = None
        self._axioms: Optional[List[Sentence]] = None
        self._goals: Optional[List[Sentence]] = None
        self._proven_goals: Optional[List[Sentence]] = None
        self._unproven_goals: Optional[List[Sentence]] = None
        self._hs_theory = hs_theory
        self._hs_pretty_sentence = prettySentence(hs_theory)

    def hs_obj(self):
        return self._hs_theory

    def hs_update(self, new_hs_obj):
        self._hs_theory = new_hs_obj

        new_sentences = OMap.toList(getAllSentences(self._hs_theory))

        for name_and_sentence in new_sentences:
            name = fst(name_and_sentence)

            if self._sentences:
                for sentence in self._sentences:
                    if sentence.name() == name:
                        sentence.hs_update(name_and_sentence)

            if self._axioms:
                for axiom in self._axioms:
                    if axiom.name() == name:
                        axiom.hs_update(name_and_sentence)

            if self._goals:
                for goal in self._goals:
                    if goal.name() == name:
                        goal.hs_update(name_and_sentence)

            if self._proven_goals:
                for proven_goal in self._proven_goals:
                    if proven_goal.name() == name:
                        proven_goal.hs_update(name_and_sentence)

            if self._unproven_goals:
                for unproven_goal in self._unproven_goals:
                    if unproven_goal.name() == name:
                        unproven_goal.hs_update(name_and_sentence)

        # Reset cached proven and unproven goals as they might have changed.
        # Previously queried goals are updated and a previously unproven goal is now proven, the instance reflects the
        # change. However, the lists should be re-queried to not list proven goals in the unproven list.
        self._proven_goals = None
        self._unproven_goals = None

    def get_usable_provers(self) -> List[Prover]:
        provers = getUsableProvers(self._hs_theory).act()
        return list({Prover(fst(p)) for p in provers})

    def get_usable_provers_with_comorphisms(self) -> Dict[Prover, List[Comorphism]]:
        provers = getUsableProvers(self._hs_theory).act()
        result = dict()
        for prover_and_comorphism in provers:
            prover = fst(prover_and_comorphism)
            comorphism = snd(prover_and_comorphism)
            result.setdefault(Prover(prover), []).append(Comorphism(comorphism))

        return result

    def get_usable_provers_and_comorphisms(self) -> List[Tuple[Prover, Comorphism]]:
        provers = getUsableProvers(self._hs_theory).act()
        return list((Prover(fst(p)), Comorphism(snd(p))) for p in provers)

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
        if self._sentences is None:
            sentences = getAllSentences(self._hs_theory)
            self._sentences = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(sentences)]

        return self._sentences

    def axioms(self) -> List[Sentence]:
        if self._axioms is None:
            axioms = getAllAxioms(self._hs_theory)
            self._axioms = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(axioms)]

        return self._axioms

    def goals(self) -> List[Sentence]:
        if self._goals is None:
            self._goals = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(getAllGoals(self._hs_theory))]

        return self._goals

    def proven_goals(self) -> List[Sentence]:
        if self._proven_goals is None:
            self._proven_goals = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(getProvenGoals(self._hs_theory))]

        return self._proven_goals

    def unproven_goals(self) -> List[Sentence]:
        if self._unproven_goals is None:
            self._unproven_goals = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(getUnprovenGoals(self._hs_theory))]

        return self._unproven_goals

    def logic(self) -> Logic:
        return Logic(logicNameOfTheory(self._hs_theory), logicDescriptionOfTheory(self._hs_theory))

    def signature(self) -> Signature:
        return Signature(signatureOfTheory(self._hs_theory))

    def sentence_by_name(self, name: str) -> Optional[Sentence]:
        return next(iter(s for s in self.sentences() if s.name() == name), None)

