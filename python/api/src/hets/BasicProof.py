from typing import Optional

from .ProofDetails import ProofDetails
from .ProofKind import ProofKind
from .haskell import PyBasicProof, PyBasicProofGuessed, PyBasicProofConjectured, PyBasicProofHandwritten, \
    pyProofStatusOfPyBasicProof, Just, fromJust


class BasicProof:
    """
    Result of proving a theory.

    Represents `Static.GTheory.BasicProof` via `HetsAPI.Python.PyBasicProof`.
    """

    def __init__(self, hs_basic_proof: PyBasicProof):
        """
        Result of proving a theory.

        :warning: This class should not be instantiated manually.

        :param hs_basic_proof: Haskell object of ``HetsAPI.Internal.BasicProof``
        """
        self._hs_basic_proof = hs_basic_proof

    def is_guessed(self) -> bool:
        """
        Returns whether the proof is guessed.
        """

        return isinstance(self._hs_basic_proof, PyBasicProofGuessed)

    def is_conjectured(self) -> bool:
        """
        Returns whether the proof is conjectured.
        """

        return isinstance(self._hs_basic_proof, PyBasicProofConjectured)

    def is_handwritten(self) -> bool:
        """
        Returns whether the proof is handwritten.
        """

        return isinstance(self._hs_basic_proof, PyBasicProofHandwritten)

    def details(self) -> Optional[ProofDetails]:
        """
        Get the details of the proof if available.

        Proof details are not available if the proof is guessed, conjectured, or handwritten.

        :return: Details of the proof
        """

        maybe = pyProofStatusOfPyBasicProof(self._hs_basic_proof)
        if isinstance(maybe, Just):
            return ProofDetails(fromJust(maybe), self._kind())

        return None

    def _kind(self) -> Optional[ProofKind]:
        if self.is_guessed():
            return ProofKind.GUESSED
        elif self.is_conjectured():
            return ProofKind.CONJECTURED
        elif self.is_handwritten():
            return ProofKind.HANDWRITTEN
        else:
            return None

    def kind(self) -> ProofKind:
        """
        Get the kind of the proof.
        """

        details = self.details()
        if details is None:
            return self._kind()
        else:
            return details.kind()
