from typing import List

from .Sentence import Sentence
from .haskell import ProofState as ProofStateHs, Diagnosis


class ProofState:
    """
    Represents the result of a proof attempt.

    Represents `Proofs.AbstractState.ProofState` via `HetsAPI.Internal.ProofState`.
    """
    def __init__(self, hs_proof_state: ProofStateHs, theory):
        self._hs_proof_state = hs_proof_state
        self._theory = theory

    def selected_goals(self) -> List[Sentence]:
        """
        Returns the selected goals of the proof state.
        :return: List selected goals
        """
        goal_names = self._hs_proof_state.selectedGoals()
        return [x for x in self._theory.goals() if x.name() in goal_names]

    def included_axioms(self) -> List[Sentence]:
        """
        Returns the included axioms of the proof state.
        :return: List of included axioms
        """
        goal_names = self._hs_proof_state.includedAxioms()
        return [x for x in self._theory.axioms() if x.name() in goal_names]

    def included_theorems(self) -> List[Sentence]:
        """
        Returns the theorems included in the proof.
        :return:
        """
        goal_names = self._hs_proof_state.includedTheorems()
        return [x for x in self._theory.sentences() if x.name() in goal_names]

    def acc_diags(self) -> List[Diagnosis]:
        """
        Returns the accumulated diagnoses occured during the proof.
        :return:
        """
        return self._hs_proof_state.accDiags()

    def selected_prover_name(self) -> str:
        """
        Returns the name of the selected prover.
        :return:
        """
        return self._hs_proof_state.selectedProver()

    def selected_cons_checker_name(self) -> str:
        """
        Returns the name of the selected consistency checker.
        :return:
        """
        return self._hs_proof_state.selectedConsChecker()
