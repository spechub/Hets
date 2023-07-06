"""
Description :  Represents `Logic.Prover.ProofStatus`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from datetime import datetime, timedelta
from enum import Enum

from .haskell import ProofStatus as ProofStatusHs, GoalStatus, TimeOfDay, tacticScriptContent, Open, Proved, Disproved, show

from typing import Any, List, Optional


class ProofKind(Enum):
    UNKNOWN = -1
    OPEN = 1
    PROVEN = 2
    PROVEN_BY_INCONSISTENCY = 3
    DISPROVEN = 4
    TIMED_OUT = 5
    GUESSED = 6
    CONJECTURED = 7
    HANDWRITTEN = 8

    def to_str(self) -> str:
        return {
            ProofKind.UNKNOWN: "Unknown",
            ProofKind.OPEN: "Open",
            ProofKind.PROVEN: "Proven",
            ProofKind.PROVEN_BY_INCONSISTENCY: "Proven by inconsistency",
            ProofKind.DISPROVEN: "Disproven",
            ProofKind.TIMED_OUT: "Timed out",
            ProofKind.GUESSED: "Guessed",
            ProofKind.CONJECTURED: "Conjectured",
            ProofKind.HANDWRITTEN: "Handwritten"
        }[self]


class ProofDetails:
    def __init__(self, hs_proof_status: ProofStatusHs, kind: Optional[ProofKind] = None):
        self._hs_proof_status = hs_proof_status

        self._kind = kind

    def goal_name(self) -> str:
        return self._hs_proof_status.goalName()

    def goal_status(self) -> GoalStatus:
        return self._hs_proof_status.goalStatus()

    def used_axioms(self) -> List[str]:
        return list(self._hs_proof_status.usedAxioms())

    def used_prover(self) -> str:
        return self._hs_proof_status.usedProver()

    def used_time(self) -> timedelta:
        used_time_str = show(self._hs_proof_status.usedTime())
        print(used_time_str)
        if used_time_str.startswith("-"):
            # Sometimes the prover returns -1 as time. Return 0 instead.
            return timedelta(seconds=-1)

        if "." in used_time_str:
            used_time_str = used_time_str.split(".")[0]

        used_time = datetime.strptime(used_time_str, "%H:%M:%S")

        return used_time - datetime.strptime("", "")

    def tactic_script(self) -> str:
        return tacticScriptContent(self._hs_proof_status.tacticScript())

    def proof_tree(self) -> str:
        return show(self._hs_proof_status.proofTree())

    def proof_lines(self) -> List[str]:
        return list(self._hs_proof_status.proofLines())

    def kind(self) -> ProofKind:
        if self._kind is not None:
            return self._kind

        status = self.goal_status()

        if isinstance(status, Open):
            if any("timeout" in reason.lower() for reason in status.goalStatusOpenReason()):
                return ProofKind.TIMED_OUT

            return ProofKind.OPEN
        if isinstance(status, Disproved):
            return ProofKind.DISPROVEN
        if isinstance(status, Proved):
            return ProofKind.PROVEN
