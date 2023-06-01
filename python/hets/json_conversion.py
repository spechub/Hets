import ast
from typing import Union

from .haskell import show, ByteString, toStrict

import json


def as_json(hs_byte_string: Union[ByteString, bytes]) -> dict:
    """
    Returns a haskell byte string as json objects.

    The union in the parameter originates from hyphen converting `Data.ByteString.ByteString` to pythons `bytes`, but
    `Data.ByteString.Lazy.ByteString` is not converted automatically.

    The JSON representation is generated automatically by the haskell package Data.Aeson.
    See https://hackage.haskell.org/package/aeson/docs/Data-Aeson.html for further details.

    @param hs_byte_string A haskell `Data.ByteString.ByteString` or `Data.ByteString.Lazy.ByteString`
    @return The byte string parsed as json object to a dictionary
    """

    if isinstance(hs_byte_string, bytes):
        json_str = hs_byte_string
    else:
        json_str = toStrict(hs_byte_string)

    json_obj = json.loads(json_str)

    return json_obj
