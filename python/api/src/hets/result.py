"""
Description :  Provides utility functions to interact with `Common.Result.Result` instances
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Any, TypeVar, Generic, Optional, List
from .haskell import resultToMaybe, fromJust, Just, show, Result, Diagnosis, diags
from .maybe import maybe_to_optional

T = TypeVar("T")


class ResultException(BaseException):
    pass


def result_to_optional(result: Generic[T]) -> Optional[T]:
    return maybe_to_optional(resultToMaybe(result))


def result_or_raise(result: Generic[T], msg: str = "An error occurred") -> T:
    result_maybe = resultToMaybe(result)
    if isinstance(result_maybe, Just):
        return fromJust(result_maybe)
    else:
        raise ResultException(f"{msg}: {show(diags(result))}")
