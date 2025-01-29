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
    """
    Exception raised when trying to extract a value from a result but the result contained an error.
    """
    pass


def result_to_optional(result: Generic[T]) -> Optional[T]:
    """
    Converts a Haskell Result object to an Optional Python object.
    :param result: Haskell Result object
    :return: Value of the result or None if the result contains an error
    """
    return maybe_to_optional(resultToMaybe(result))


def result_or_raise(result: Generic[T], msg: str = "An error occurred") -> T:
    """
    Extracts the value from a result or raises a `ResultException` if the result contains an error.
    :param result: Haskell Result object
    :param msg: Message to include in the exception
    :return:
    """
    result_maybe = resultToMaybe(result)
    if isinstance(result_maybe, Just):
        return fromJust(result_maybe)
    else:
        raise ResultException(f"{msg}: {show(diags(result))}")
