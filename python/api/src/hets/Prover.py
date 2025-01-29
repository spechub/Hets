from typing import Optional, List

from .haskell import proverName, PyProver, PyComorphism


class Prover:
    """
    Represents a prover.

    Represents `Logic.Prover.Prover`
    """

    def __init__(self, hs_prover: PyProver) -> None:
        self._hs_prover = hs_prover

    def name(self) -> str:
        """
        Returns the name of the prover.
        :return:
        """
        return proverName(self._hs_prover)

    def __eq__(self, other):
        return isinstance(other, Prover) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()

    def __repr__(self):
        return f"<{__name__} '{self.name()}'>"

