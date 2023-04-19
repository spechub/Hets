"""
Description :  Represents `Logic.Prover.ConsChecker`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from .haskell import getConsCheckerName, PyConsChecker

class ConsistencyChecker:
    def __init__(self, hsConsChecker: PyConsChecker) -> None:
        self._hsConsChecker = hsConsChecker

    def name(self) -> str:
        return getConsCheckerName(self._hsConsChecker)

    def __eq__(self, other):
        return isinstance(other, ConsistencyChecker) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()
