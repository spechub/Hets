"""
Description :  Represents `Logic.Comorphism`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from .haskell import comorphismName, PyComorphism


class Comorphism:
    def __init__(self, hs_comorphism: PyComorphism) -> None:
        """
        A comorphism from one logic to another.

        :warning: This class should not be instantiated manually.

        :param hs_comorphism: Haskell object of ``HetsAPI.Python.PyComorphism``
        """

        self._hs_comorphism = hs_comorphism

    def name(self) -> str:
        """
        Get the name of the comorphism.
        """

        return comorphismName(self._hs_comorphism)

    def __eq__(self, other):
        return isinstance(other, Comorphism) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()

    def path_length(self) -> int:
        """
        Calculates the length of the comorphism path.
        """

        return len(self.name().split(";"))
