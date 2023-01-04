from typing import Any

from hs.Common.Result import Result, resultToMaybe
from hs.Prelude import Just, fromJust, show


def resultOrRaise(result: Result, msg: str = "An error occured") -> Any:
    resultM = resultToMaybe(result)
    if isinstance(resultM, Just):
        return fromJust(resultM)
    else:
        raise Exception(f"{msg}: {show(result.diags())}")
