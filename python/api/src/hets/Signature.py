from typing import Set, List

from .json_conversion import as_json
from .haskell import ExtSign


class Signature:
    def __init__(self, hs_signature: ExtSign):
        self._hs_signature = hs_signature

    def non_imported_symbols(self) -> List[dict]:
        return [as_json(symbol) for symbol in self._hs_signature.nonImportedSymbols()]

    def plain(self) -> dict:
        return as_json(self._hs_signature.plainSign())
