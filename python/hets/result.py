"""
Description :  Provides utility functions to interact with `Common.Result.Result` instances
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Any, TypeVar, Generic
from .haskell import Result, resultToMaybe, fromJust, Just, show

T = TypeVar("T")


def resultOrRaise(result: Generic[T], msg: str = "An error occured") -> T:
    resultM = resultToMaybe(result)
    if isinstance(resultM, Just):
        return fromJust(resultM)
    else:
        raise Exception(f"{msg}: {show(result.diags())}")
