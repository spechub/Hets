import typing

from .haskell import fromJust, Maybe, Just

T = typing.TypeVar("T")


def maybe_to_optional(maybe: typing.Generic[T]) -> typing.Optional[T]:
    if isinstance(maybe, Just):
        return fromJust(maybe)

    return None
