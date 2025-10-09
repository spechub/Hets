import typing

from .haskell import fromJust, Maybe, Just

T = typing.TypeVar("T")


def maybe_to_optional(maybe: typing.Generic[T]) -> typing.Optional[T]:
    """
    Converts a Haskell Maybe object to an Optional.
    :param maybe: Haskell Maybe object
    :return: Value if Just, None if Nothing
    """
    if isinstance(maybe, Just):
        return fromJust(maybe)

    return None
