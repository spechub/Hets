from typing import Tuple, Optional

from .haskell import DGLinkLab, fstOf3, sndOf3, thd
from .HsWrapper import HsHierarchyElement


class DevGraphEdge(HsHierarchyElement):
    def __init__(self, hsEdge: Tuple[int, int, DGLinkLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hsEdge = hsEdge

    def hsObj(self):
        return self._hsEdge

    def origin(self) -> int:
        return fstOf3(self._hsEdge)

    def target(self) -> int:
        return sndOf3(self._hsEdge)

    def label(self) -> DGLinkLab:
        return thd(self._hsEdge)

    def name(self):
        return self.label().dglName()
