"""
Description :  Represents `Logic.Comorphism`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from .haskell import comorphismName, PyComorphism


class Comorphism:
    def __init__(self, hsComorphism: PyComorphism) -> None:
        self._hsComorphism = hsComorphism

    def name(self) -> str:
        return comorphismName(self._hsComorphism)

    def __eq__(self, other):
        return isinstance(other, Comorphism) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()
