"""
Description :  Represents `Logic.Prover.ProofStatus`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from .haskell import ProofStatus as ProofStatusHs, GoalStatus, TimeOfDay, TacticScript

from typing import Any, List


class ProofStatus:
    def __init__(self, hs_proof_status: ProofStatusHs):
        self._hs_proof_status = hs_proof_status

    def goal_name(self) -> str:
        return self._hs_proof_status.goalName()

    def goal_status(self) -> GoalStatus:
        return self._hs_proof_status.goalStatus()

    def used_axioms(self) -> List[str]:
        return self._hs_proof_status.usedAxioms()

    def used_prover(self) -> str:
        return self._hs_proof_status.usedProver()

    def used_time(self) -> TimeOfDay:
        return self._hs_proof_status.usedTime()

    def tactic_script(self) -> TacticScript:
        return self._hs_proof_status.tacticScript()

    def proof_lines(self) -> List[str]:
        return self._hs_proof_status.proofLines()

