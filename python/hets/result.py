from typing import Any, TypeVar
from .haskell import Result, resultToMaybe, fromJust, Just, show

T = TypeVar("T")


def resultOrRaise(result: Result, msg: str = "An error occured") -> T:
    resultM = resultToMaybe(result)
    if isinstance(resultM, Just):
        return fromJust(resultM)
    else:
        raise Exception(f"{msg}: {show(result.diags())}")
