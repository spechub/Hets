"""
Description :  Represents `Proofs.AbstractState.ProofState`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import List

from .Sentence import Sentence
from .haskell import ProofState as ProofStateHs, Diagnosis


class ProofState:
    def __init__(self, hsProofState: ProofStateHs, theory):
        self._hsProofState = hsProofState
        self._theory = theory

    def selectedGoals(self) -> List[Sentence]:
        goalNames = self._hsProofState.selectedGoals()
        return [ x for x in self._theory.goals() if x.name() in goalNames ]

    def includedAxioms(self) -> List[Sentence]:
        goalNames = self._hsProofState.includedAxioms()
        return [ x for x in self._theory.axioms() if x.name() in goalNames ]

    def includedTheorems(self) -> List[Sentence]:
        goalNames = self._hsProofState.includedTheorems()
        return [ x for x in self._theory.sentences() if x.name() in goalNames ]

    def accDiags(self) -> List[Diagnosis]:
        return self._hsProofState.accDiags()

    def selectedProverName(self) -> str:
        return self._hsProofState.selectedProver()

    def selectedConsCheckerName(self) -> str:
        return self._hsProofState.selectedConsChecker()
