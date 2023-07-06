"""
Description :  Represents `Logic.Logic.Sentences`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
import json
from typing import Tuple, Callable, List, Optional

from .maybe import maybe_to_optional
from .haskell import fst, snd, PyTheorySentence, Sentence as PySentence, PyBasicProof, theorySentenceIsAxiom, \
    theorySentenceWasTheorem, theorySentenceIsDefined, theorySentenceGetTheoremStatus, theorySentencePriority, \
    theorySentenceContent, Just, fromJust, theorySentenceBestProof
from .json_conversion import as_json

from .Comorphism import Comorphism
from .BasicProof import BasicProof
from .ProofDetails import ProofDetails, ProofKind

from .HsWrapper import HsHierarchyElement


class Sentence(HsHierarchyElement):
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
        return self._name

    def as_json(self) -> dict:
        return as_json(theorySentenceContent(self._hs_sentence))

    def is_axiom(self) -> bool:
        return theorySentenceIsAxiom(self._hs_sentence)

    def was_theorem(self) -> bool:
        return theorySentenceWasTheorem(self._hs_sentence)

    def is_defined(self) -> bool:
        return theorySentenceIsDefined(self._hs_sentence)

    def is_proven(self) -> bool:
        return any(b.kind() == ProofKind.PROVEN for _, b in self.theorem_status())

    def theorem_status(self) -> List[Tuple[Comorphism, BasicProof]]:
        return list((Comorphism(fst(x)), BasicProof(snd(x))) for x in theorySentenceGetTheoremStatus(self._hs_sentence))

    def best_proof(self) -> Optional[BasicProof]:
        proof = maybe_to_optional(theorySentenceBestProof(self._hs_sentence))
        return BasicProof(proof) if proof is not None else None

    def priority(self) -> Optional[str]:
        priority = theorySentencePriority(self._hs_sentence)
        if isinstance(priority, Just):
            return fromJust(priority)

        return None

    def __str__(self) -> str:
        return self._hs_pretty_fn(theorySentenceContent(self._hs_sentence))

    def __repr__(self):
        return f"<{__name__} object representing sentence {self.name()} = '{str(self)}'>"
