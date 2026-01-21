from .haskell.Python import conservativityCheckerName, conservativityCheckerUsable

from .maybe import maybe_to_optional


class ConservativityChecker:
    def __init__(self, hs_conservativity_checker):
        self._hs_cons_checker = hs_conservativity_checker

    def name(self) -> str:
        return conservativityCheckerName(self._hs_cons_checker)

    def get_usable(self) -> bool:
        res = conservativityCheckerUsable(self._hs_cons_checker).act()
        return maybe_to_optional(res) is None
