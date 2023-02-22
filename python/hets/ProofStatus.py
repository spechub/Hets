from .haskell import ProofStatus as ProofStatusHs, GoalStatus, TimeOfDay, TacticScript

from typing import Any, List


class ProofStatus:
    def __init__(self, hsProofStatus: ProofStatusHs[Any]):
        self._hsProofStatus = hsProofStatus

    def goalName(self) -> str:
        return self._hsProofStatus.goalName()

    def goalStatus(self) -> GoalStatus:
        return self._hsProofStatus.goalStatus()

    def usedAxioms(self) -> List[str]:
        return self._hsProofStatus.usedAxioms()

    def usedProver(self) -> str:
        return self._hsProofStatus.usedProver()

    def usedTime(self) -> TimeOfDay:
        return self._hsProofStatus.usedTime()

    def tacticScript(self) -> TacticScript:
        return self._hsProofStatus.tacticScript()

    def proofLines(self) -> List[str]:
        return self._hsProofStatus.proofLines()

