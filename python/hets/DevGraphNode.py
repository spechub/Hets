from typing import Tuple

from .haskell import snd, getTheoryFromNode, DGNodeLab

from .Theory import Theory


class DevGraphNode:
    def __init__(self, hsNode: Tuple[int, DGNodeLab], hsAutoCheckConsistency) -> None:
        self._hsNode = hsNode
        self._hsAutoCheckConsistency = hsAutoCheckConsistency(hsNode)

    def theory(self) -> Theory:
        return Theory(getTheoryFromNode(snd(self._hsNode)), self._hsAutoCheckConsistency)
