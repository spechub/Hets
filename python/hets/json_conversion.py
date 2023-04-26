from .haskell import show

import json


def as_json(hs_byte_string) -> dict:
    """
    Returns the sentences as json objects.

    The JSON representation is generated automatically by the haskell package
    Data.Aeson.
    See https://hackage.haskell.org/package/aeson/docs/Data-Aeson.html
    for further details.
    """

    # Get json.
    # Return type is ByteString which is not converted to either pythons
    # `bytes` or `str` type. Hence, the conversion via `show` and
    # `encode.decode`. [1:-1] to exclude the quotation marks added by `show`
    json_str = show(hs_byte_string).encode("utf-8").decode("unicode_escape")[1:-1]
    json_obj = json.loads(json_str)

    return json_obj
