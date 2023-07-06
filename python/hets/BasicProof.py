from typing import Optional

from .ProofDetails import ProofDetails, ProofKind
from .haskell import PyBasicProof, PyBasicProofGuessed, PyBasicProofConjectured, PyBasicProofHandwritten, \
    pyProofStatusOfPyBasicProof, Just, fromJust


class BasicProof:
    def __init__(self, hs_basic_proof: PyBasicProof):
        self._hs_basic_proof = hs_basic_proof

    def is_guessed(self) -> bool:
        return isinstance(self._hs_basic_proof, PyBasicProofGuessed)

    def is_conjectured(self) -> bool:
        return isinstance(self._hs_basic_proof, PyBasicProofConjectured)

    def is_handwritten(self) -> bool:
        return isinstance(self._hs_basic_proof, PyBasicProofHandwritten)

    def details(self) -> Optional[ProofDetails]:
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
        details = self.details()
        if details is None:
            return self._kind()
        else:
            return details.kind()
