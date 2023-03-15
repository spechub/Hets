from typing import Tuple, Optional

from .HsWrapper import HsHierarchyElement
from .haskell import snd, getTheoryFromNode, DGNodeLab, fst

from .Theory import Theory


class DevGraphNode(HsHierarchyElement):
    def __init__(self, hsNode: Tuple[int, DGNodeLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hsNode = hsNode

        self._theory: Optional[Theory] = None

    def hsObj(self):
        return self._hsNode

    def id(self):
        return fst(self._hsNode)

    def label(self):
        return snd(self._hsNode)

    def hsUpdate(self, newHsObj):
        self._hsNode = newHsObj

        if self._theory:
            nodeLab = snd(self._hsNode)
            hsTheory = getTheoryFromNode(nodeLab)
            self._theory.hsUpdate(hsTheory)

    def theory(self) -> Theory:
        if self._theory is None:
            self._theory = Theory(getTheoryFromNode(snd(self._hsNode)), self)

        return self._theory
