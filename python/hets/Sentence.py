"""
Description :  Represents `Logic.Logic.Sentences`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
import json
from typing import Tuple, Callable

from .haskell import fst, show, snd, Sentence as PySentence


class Sentence:
    def __init__(self, hsSentenceWithName: Tuple[str, PySentence], hsPrettyFn: Callable[[PySentence], str]) -> None:
        self._name = fst(hsSentenceWithName)
        self._hsSentence = snd(hsSentenceWithName)
        self._hsPrettyFn = hsPrettyFn

    def name(self) -> str:
        return self._name
    
    def as_json(self) -> dict:
        '''
        Returns the sentences as json objects.
        
        The JSON representation is generated automatically by the haskell package
        Data.Aeson.
        See https://hackage.haskell.org/package/aeson/docs/Data-Aeson.html
        for further details.
        '''
        
        # Get json.
        # Return type is ByteString which is not converted to either pythons
        # `bytes` or `str` type. Hence the conversion via `show` and
        # `encode.decode`. [1:-1] to exclude the quotation marks added by `show`
        
        json_str = show(self._hsSentence).encode("utf-8").decode("unicode_escape")[1:-1]
        json_obj = json.loads(json_str)
        
        return json_obj

    def __str__(self) -> str:
        return self._hsPrettyFn(self._hsSentence)

    def __repr__(self):
        return f"<{__name__} object representing sentence {self.name()} = '{str(self)}'>"
