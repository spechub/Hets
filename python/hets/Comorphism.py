from .haskell import getComorphismName, PyComorphism


class Comorphism:
    def __init__(self, hsComorphism: PyComorphism) -> None:
        self._hsComorphism = hsComorphism

    def name(self) -> str:
        return getComorphismName(self._hsComorphism)

    def __eq__(self, other):
        return isinstance(other, Comorphism) and self.name() == other.name()

    def __hash__(self):
        return self.name().__hash__()