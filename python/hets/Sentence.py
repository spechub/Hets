"""
Description :  Represents `Logic.Logic.Sentences`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
import json
from typing import Tuple, Callable

from .haskell import fst, show, snd, Sentence as PySentence
from .json_conversion import as_json


class Sentence:
    def __init__(self, hs_sentence_with_name: Tuple[str, PySentence], hs_pretty_fn: Callable[[PySentence], str]) -> None:
        self._name = fst(hs_sentence_with_name)
        self._hs_sentence = snd(hs_sentence_with_name)
        self._hs_pretty_fn = hs_pretty_fn

    def name(self) -> str:
        return self._name
    
    def as_json(self) -> dict:
        return as_json(self._hs_sentence)

    def __str__(self) -> str:
        return self._hs_pretty_fn(self._hs_sentence)

    def __repr__(self):
        return f"<{__name__} object representing sentence {self.name()} = '{str(self)}'>"
