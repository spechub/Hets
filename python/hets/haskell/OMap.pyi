from typing import List, Any, TypeVar, Generic

K = TypeVar("K")
V = TypeVar("V")

class OMap(Generic[K, V]): ...


def toList(m: OMap[K, V])-> List[(K, V)]: ...
