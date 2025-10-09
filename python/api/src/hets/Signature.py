from typing import Set, List

from .json_conversion import as_json
from .haskell import ExtSign


class Signature:
    """
    Represents a signature.

    Represents `Logic.Signature.Signature` via `HetsAPI.Python.ExtSign`.
    """
    def __init__(self, hs_signature: ExtSign):
        self._hs_signature = hs_signature

    def non_imported_symbols(self) -> List[dict]:
        """
        Returns the non-imported symbols of the signature as JSON objects.
        :return:
        """
        return [as_json(symbol) for symbol in self._hs_signature.nonImportedSymbols()]

    def plain(self) -> dict:
        """
        Returns the plain signature as a JSON object.
        :return:
        """
        return as_json(self._hs_signature.plainSign())
