from typing import TypeVar, Generic

from .haskell import showDoc

A = TypeVar("A")


class Pretty(Generic[A]):
    def __init__(self, hs_obj):
        self._hs_obj = hs_obj

    def to_str(self) -> str:
        return showDoc(self._hs_obj)("")

    def __eq__(self, other):
        return isinstance(other, Pretty) and other.to_str() == self.to_str()

    def __hash__(self):
        return hash(self.to_str())
