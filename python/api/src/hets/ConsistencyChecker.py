"""
Description :  Represents `Logic.Prover.ConsChecker`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from .haskell import consCheckerName, PyConsChecker


class ConsistencyChecker:
    def __init__(self, hs_cons_checker: PyConsChecker) -> None:
        """
        A tool to check the consistency of a theory.

        :warning: This class should not be instantiated manually.

        :param hs_cons_checker: Haskell object of ``HetsAPI.Python.PyConsChecker``
        """

        self._hs_cons_checker = hs_cons_checker

    def name(self) -> str:
        """
        Get the name of the consistency checker
        """

        return consCheckerName(self._hs_cons_checker)

    def __eq__(self, other):
        return isinstance(other, ConsistencyChecker) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()
