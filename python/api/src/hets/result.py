"""
Description :  Provides utility functions to interact with `Common.Result.Result` instances
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Any, TypeVar, Generic
from .haskell import resultToMaybe, fromJust, Just, show

T = TypeVar("T")


def result_or_raise(result: Generic[T], msg: str = "An error occured") -> T:
    result_maybe = resultToMaybe(result)
    if isinstance(result_maybe, Just):
        return fromJust(result_maybe)
    else:
        raise Exception(f"{msg}: {show(result.diags())}")
