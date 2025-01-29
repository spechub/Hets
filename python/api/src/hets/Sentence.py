import json
from typing import Tuple, Callable, List, Optional

from .maybe import maybe_to_optional
from .haskell import fst, snd, PyTheorySentence, Sentence as PySentence, PyBasicProof, theorySentenceIsAxiom, \
    theorySentenceWasTheorem, theorySentenceIsDefined, theorySentenceGetTheoremStatus, theorySentencePriority, \
    theorySentenceContent, Just, fromJust, theorySentenceBestProof
from .json_conversion import as_json

from .Comorphism import Comorphism
from .BasicProof import BasicProof
from .ProofDetails import ProofDetails
from hets import ProofKind

from .HsWrapper import HsHierarchyElement


class Sentence(HsHierarchyElement):
    """
    Represents a sentence in a theory.

    Represents `Logic.Logic.Sentence` via `HetsAPI.Python.PyTheorySentence`.
    """
    def __init__(self, hs_sentence_with_name: Tuple[str, PyTheorySentence],
                 hs_pretty_fn: Callable[[PySentence], str],
                 parent: Optional[HsHierarchyElement] = None) -> None:
        super().__init__(parent)
        self._hs_obj = hs_sentence_with_name
        self._name = fst(hs_sentence_with_name)
        self._hs_sentence = snd(hs_sentence_with_name)
        self._hs_pretty_fn = hs_pretty_fn

    def hs_obj(self):
        return self._hs_obj

    def hs_update(self, new_hs_obj):
        self._hs_obj = new_hs_obj
        self._name = fst(new_hs_obj)
        self._hs_sentence = snd(new_hs_obj)

    def name(self) -> str:
        """
        Returns the name of the sentence.
        :return:
        """
        return self._name

    def as_json(self) -> dict:
        """
        Converts the sentence to a JSON object.
        :return:
        """
        return as_json(theorySentenceContent(self._hs_sentence))

    def is_axiom(self) -> bool:
        """
        Returns whether the sentence is an axiom.
        :return: True if the sentence is an axiom, False otherwise
        """
        return theorySentenceIsAxiom(self._hs_sentence)

    def was_theorem(self) -> bool:
        """
        Returns whether the sentence was a goal but was proven and included as axiom in a proof.
        :return: True if the sentence originally was a goal
        """
        return theorySentenceWasTheorem(self._hs_sentence)

    def is_defined(self) -> bool:
        """
        Returns whether the sentence is defined. TODO: Reallly?
        :return:
        """
        return theorySentenceIsDefined(self._hs_sentence)

    def is_proven(self) -> bool:
        """
        Returns whether the sentence is proven.
        :return:
        """
        return any(b.kind() == ProofKind.PROVEN for _, b in self.theorem_status())

    def theorem_status(self) -> List[Tuple[Comorphism, BasicProof]]:
        """
        Returns the theorem status of the sentence.
        :return:
        """
        return list((Comorphism(fst(x)), BasicProof(snd(x))) for x in theorySentenceGetTheoremStatus(self._hs_sentence))

    def best_proof(self) -> Optional[BasicProof]:
        """
        Returns the best proof of the sentence.
        :return:
        """
        proof = maybe_to_optional(theorySentenceBestProof(self._hs_sentence))
        return BasicProof(proof) if proof is not None else None

    def priority(self) -> Optional[str]:
        """
        Returns the priority of the sentence if it has one.
        :return:
        """

        priority = theorySentencePriority(self._hs_sentence)
        if isinstance(priority, Just):
            return fromJust(priority)

        return None

    def __str__(self) -> str:
        return self._hs_pretty_fn(theorySentenceContent(self._hs_sentence))

    def __repr__(self):
        return f"<{__name__} object representing sentence {self.name()} = '{str(self)}'>"
