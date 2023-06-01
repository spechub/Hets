"""
Description :  Represents `Proofs.AbstractState.ProofState`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import List

from .Sentence import Sentence
from .haskell import ProofState as ProofStateHs, Diagnosis


class ProofState:
    def __init__(self, hs_proof_state: ProofStateHs, theory):
        self._hs_proof_state = hs_proof_state
        self._theory = theory

    def selected_goals(self) -> List[Sentence]:
        goal_names = self._hs_proof_state.selectedGoals()
        return [x for x in self._theory.goals() if x.name() in goal_names]

    def included_axioms(self) -> List[Sentence]:
        goal_names = self._hs_proof_state.includedAxioms()
        return [x for x in self._theory.axioms() if x.name() in goal_names]

    def included_theorems(self) -> List[Sentence]:
        goal_names = self._hs_proof_state.includedTheorems()
        return [x for x in self._theory.sentences() if x.name() in goal_names]

    def acc_diags(self) -> List[Diagnosis]:
        return self._hs_proof_state.accDiags()

    def selected_prover_name(self) -> str:
        return self._hs_proof_state.selectedProver()

    def selected_cons_checker_name(self) -> str:
        return self._hs_proof_state.selectedConsChecker()
