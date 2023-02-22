from typing import Tuple, Callable

from .haskell import fst, snd, Sentence as PySentence


class Sentence:
    def __init__(self, hsSentenceWithName: Tuple[str, PySentence], hsPrettyFn: Callable[[PySentence], str]) -> None:
        self._name = fst(hsSentenceWithName)
        self._hsSentence = snd(hsSentenceWithName)
        self._hsPrettyFn = hsPrettyFn

    def name(self) -> str:
        return self._name

    def __str__(self) -> str:
        return self._hsPrettyFn(self._hsSentence)

    def __repr__(self):
        return f"<{__name__} object representing sentence {self.name()} = '{str(self)}'>"
