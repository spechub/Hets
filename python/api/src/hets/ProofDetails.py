from datetime import datetime, timedelta

from .haskell import ProofStatus as ProofStatusHs, GoalStatus, tacticScriptContent, Open, Proved, Disproved, show

from .ProofKind import ProofKind

from typing import List, Optional


class ProofDetails:
    """
    Represents the details of a proof.

    Represents `Logic.Prover.ProofStatus` via `HetsAPI.Internal.ProofStatus`.
    """
    def __init__(self, hs_proof_status: ProofStatusHs, kind: Optional[ProofKind] = None):
        self._hs_proof_status = hs_proof_status

        self._kind = kind

    def goal_name(self) -> str:
        """
        Returns the name of the goal that was attempted to be proven.
        :return:
        """
        return self._hs_proof_status.goalName()

    def goal_status(self) -> GoalStatus:
        """
        Returns the status of the goal as a result of the proof.
        :return:
        """
        return self._hs_proof_status.goalStatus()

    def used_axioms(self) -> List[str]:
        """
        Returns the axioms that were used in the proof.
        :return: List of names of axioms in the theory
        """
        return list(self._hs_proof_status.usedAxioms())

    def used_prover(self) -> str:
        """
        Returns the prover that was used in the proof.
        :return: Name of the prover
        """
        return self._hs_proof_status.usedProver()

    def used_time(self) -> timedelta:
        """
        Returns the elapsed time of the proof.
        :return:
        """
        used_time_str = show(self._hs_proof_status.usedTime())
        if used_time_str.startswith("-"):
            # Sometimes the prover returns -1 as time. Return 0 instead.
            return timedelta(seconds=-1)

        if "." in used_time_str:
            used_time_str = used_time_str.split(".")[0]

        used_time = datetime.strptime(used_time_str, "%H:%M:%S")

        return used_time - datetime.strptime("", "")

    def tactic_script(self) -> str:
        """
        Returns the tactic script that was used in the proof.
        :return:
        """
        return tacticScriptContent(self._hs_proof_status.tacticScript())

    def proof_tree(self) -> str:
        """
        Returns the proof tree of the proof if available.
        :return: String representation of the proof tree or an empty string if not available
        """
        return show(self._hs_proof_status.proofTree())

    def proof_lines(self) -> List[str]:
        """
        Returns the proof lines of the proof or an empty list if not available.
        :return:
        """
        return list(self._hs_proof_status.proofLines())

    def kind(self) -> ProofKind:
        """
        Returns the result kind of the proof.
        :return:
        """
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
