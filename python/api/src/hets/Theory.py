from __future__ import annotations

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
                      prettySentence, showTheory,
                      getUnprovenGoals, OMap, snd,
                      logicNameOfTheory,
                      logicDescriptionOfTheory, signatureOfTheory, sublogicOfPyTheory, getTheoryForSelection,
                      translateTheory)
from .result import result_or_raise


class Theory(HsHierarchyElement):
    """
    Represents a logical theory.

    Represents `Static.GTheory.G_theory` via `HetsAPI.Python.PyTheory`.
    """

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
        """
        Get all usable provers for the theory.
        :return: List of usable provers
        """
        provers = getUsableProvers(self._hs_theory).act()
        return list({Prover(fst(p)) for p in provers})

    def get_usable_provers_with_comorphisms(self) -> Dict[Prover, List[Comorphism]]:
        """
        Get all usable provers for the theory with their comorphisms.
        :return: Dictionary with provers as keys and lists of suitable comorphisms as values
        """
        provers = getUsableProvers(self._hs_theory).act()
        result = dict()
        for prover_and_comorphism in provers:
            prover = fst(prover_and_comorphism)
            comorphism = snd(prover_and_comorphism)
            result.setdefault(Prover(prover), []).append(Comorphism(comorphism))

        return result

    def get_usable_provers_and_comorphisms(self) -> List[Tuple[Prover, Comorphism]]:
        """
        Get all usable provers for the theory with their comorphisms.
        :return: List of tuples of a prover and a suitable comorphisms
        """
        provers = getUsableProvers(self._hs_theory).act()
        return list((Prover(fst(p)), Comorphism(snd(p))) for p in provers)

    def get_prover_by_name(self, name: str) -> Optional[Prover]:
        """
        Get a prover by its name.
        :param name: Name of the prover
        :return: The Prover if found, otherwise None
        """
        matches = list(p for p in self.get_usable_provers() if p.name() == name)
        if len(matches) == 1:
            return matches[0]
        return None

    def get_usable_consistency_checkers_with_comorphisms(self) -> Dict[ConsistencyChecker, List[Comorphism]]:
        """
        Get all usable consistency checkers for the theory with their comorphisms.
        :return: Dictionary with consistency checkers as keys and lists of suitable comorphisms as values
        """
        consistency_checkers = getUsableConsistencyCheckers(self._hs_theory).act()
        result = dict()
        for consistency_checker_and_comorphism in consistency_checkers:
            cc = fst(consistency_checker_and_comorphism)
            comorphism = snd(consistency_checker_and_comorphism)
            result.setdefault(ConsistencyChecker(cc), []).append(Comorphism(comorphism))

        return result

    def get_usable_consistency_checkers(self) -> List[ConsistencyChecker]:
        """
        Get all usable consistency checkers for the theory.
        :return:
        """
        ccs = getUsableConsistencyCheckers(self._hs_theory).act()
        return list({ConsistencyChecker(fst(cc)) for cc in ccs})

    def get_usable_consistency_checkers_and_comorphisms(self) -> List[Tuple[ConsistencyChecker, Comorphism]]:
        """
        Get all usable consistency checkers for the theory with their comorphisms.
        :return: List of tuples of a consistency checker and a suitable comorphisms
        """
        consistency_checkers = getUsableConsistencyCheckers(self._hs_theory).act()
        return list((ConsistencyChecker(fst(cc)), Comorphism(snd(cc))) for cc in consistency_checkers)

    def get_consistency_checker_by_name(self, name: str) -> Optional[ConsistencyChecker]:
        """
        Get a consistency checker by its name.
        :param name: Name of the consistency checker
        :return: The ConsistencyChecker if found, otherwise None
        """
        checkers = self.get_usable_consistency_checkers()
        return next((cc for cc in checkers if cc.name() == name), None)

    def get_available_comorphisms(self) -> List[Comorphism]:
        """
        Get all available comorphisms for the theory.
        :return:
        """
        comorphisms = getAvailableComorphisms(self._hs_theory)
        return [Comorphism(x) for x in comorphisms]

    def sentence_by_name(self, name: str) -> Optional[Sentence]:
        """
        Get a sentence by its name.

        :param name: Name of the sentence
        :return: The Sentence if found, otherwise None
        """
        return next((s for s in self.sentences() if s.name() == name), None)

    def sentences(self) -> List[Sentence]:
        """
        Get all sentences in the theory.
        :return:
        """
        if self._sentences is None:
            sentences = getAllSentences(self._hs_theory)
            self._sentences = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(sentences)]

        return self._sentences

    def axioms(self) -> List[Sentence]:
        """
        Get all axioms in the theory.
        :return:
        """
        if self._axioms is None:
            axioms = getAllAxioms(self._hs_theory)
            self._axioms = [Sentence(x, self._hs_pretty_sentence, self) for x in OMap.toList(axioms)]

        return self._axioms

    def goals(self) -> List[Sentence]:
        """
        Get all goals in the theory.
        :return:
        """
        if self._goals is None:
            self._goals = [Sentence(x, self._hs_pretty_sentence, self) for x in
                           OMap.toList(getAllGoals(self._hs_theory))]

        return self._goals

    def proven_goals(self) -> List[Sentence]:
        """
        Get all proven goals in the theory.
        :return:
        """
        if self._proven_goals is None:
            self._proven_goals = [Sentence(x, self._hs_pretty_sentence, self) for x in
                                  OMap.toList(getProvenGoals(self._hs_theory))]

        return self._proven_goals

    def unproven_goals(self) -> List[Sentence]:
        """
        Get all unproven goals in the theory.
        :return:
        """
        if self._unproven_goals is None:
            self._unproven_goals = [Sentence(x, self._hs_pretty_sentence, self) for x in
                                    OMap.toList(getUnprovenGoals(self._hs_theory))]

        return self._unproven_goals

    def logic(self) -> Logic:
        """
        Get the logic of the theory.
        :return:
        """
        return Logic(logicNameOfTheory(self._hs_theory), logicDescriptionOfTheory(self._hs_theory))

    def signature(self) -> Signature:
        """
        Get the signature of the theory.
        :return:
        """
        return Signature(signatureOfTheory(self._hs_theory))

    def sentence_by_name(self, name: str) -> Optional[Sentence]:
        """
        Get a sentence by its name.
        :param name: Name of the sentence
        :return: The Sentence if found, otherwise None
        """
        return next(iter(s for s in self.sentences() if s.name() == name), None)

    def get_sublogic(self) -> str:
        """
        Calculate and return the sublogic of the theory.
        :return:
        """
        return sublogicOfPyTheory(self._hs_theory)

    def with_selection(self,
                       axioms: Optional[List[str]] = None,
                       goals: Optional[List[str]] = None,
                       theorems: Optional[List[str]] = None):
        """
        Create a new theory with a subset of axioms, goals and theorems.

        :param axioms: Selection of axioms for the new theory
        :param goals: Selection of goals for the new theory
        :param theorems: Selection of theorems for the new theory
        :return: New theory with the selected sentences
        """
        if axioms is None:
            axioms = self.axioms()
        if goals is None:
            goals = self.goals()
        if theorems is None:
            theorems = []

        theory = getTheoryForSelection(axioms, goals, theorems, self._hs_theory)

        return Theory(theory, self.parent())

    def translate(self, comorphism: Comorphism) -> Theory:
        """
        Translate the theory using a comorphism.

        :param comorphism: Comorphism to use for the translation
        :return: The translated theory
        """
        translated_result = translateTheory(comorphism._hs_comorphism, self._hs_theory)
        translatedHs = result_or_raise(translated_result, f"Translation with '{comorphism.name()}' failed")
        translated = Theory(translatedHs, None)

        return translated

    def __str__(self) -> str:
        return showTheory(self._hs_theory)
