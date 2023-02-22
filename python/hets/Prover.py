from typing import Optional, List

from .haskell import getProverName, PyProver, PyComorphism


class Prover:
    def __init__(self, hsProver: PyProver) -> None:
        self._hsProver = hsProver

    def name(self) -> str:
        return getProverName(self._hsProver)

    def __eq__(self, other):
        return isinstance(other, Prover) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()

