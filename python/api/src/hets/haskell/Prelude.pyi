import typing

a = typing.TypeVar("a")
b = typing.TypeVar("b")

class Maybe(typing.Generic[a]): ...


class Just(Maybe[a]):
    def __init__(self, x: a): ...


class Nothing(Maybe[a]):
    def __init__(self): ...

class IO(typing.Generic[a]):
    def act(self) -> a: ...


def show(x: typing.Any) -> str: ...


def fst(tuple: typing.Tuple[a, b]) -> a: ...


def snd(tuple: typing.Tuple[a, b]) -> b: ...
