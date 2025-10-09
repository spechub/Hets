from .haskell.Python import conservativityCheckerName, conservativityCheckerUsable

from .maybe import maybe_to_optional


class ConservativityChecker:
    """
    A tool to check the conservativity of a theory.

    Represents `Proofs.AbstractState.G_cons_checker` via `HetsAPI.Python.PyConsChecker`.
    """

    def __init__(self, hs_conservativity_checker):
        self._hs_cons_checker = hs_conservativity_checker

    def name(self) -> str:
        """
        Returns the name of the conservativity checker.
        :return:
        """
        return conservativityCheckerName(self._hs_cons_checker)

    def get_usable(self) -> bool:
        """
        Returns whether the conservativity checker is usable.
        :return:
        """
        res = conservativityCheckerUsable(self._hs_cons_checker).act()
        return maybe_to_optional(res) is None
