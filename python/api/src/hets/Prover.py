"""
Description :  Represents `Logic.Prover.Prover`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Optional, List

from .haskell import proverName, PyProver, PyComorphism


class Prover:
    def __init__(self, hs_prover: PyProver) -> None:
        self._hs_prover = hs_prover

    def name(self) -> str:
        return proverName(self._hs_prover)

    def __eq__(self, other):
        return isinstance(other, Prover) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()

    def __repr__(self):
        return f"<{__name__} '{self.name()}'>"

