"""
Description :  Represents `Static.DevGraph.DGLinkLab`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Tuple, Optional

from .haskell import DGLinkLab, fstOf3, sndOf3, thd
from .HsWrapper import HsHierarchyElement


class DevGraphEdge(HsHierarchyElement):
    def __init__(self, hs_edge: Tuple[int, int, DGLinkLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hs_edge = hs_edge

    def hs_obj(self):
        return self._hs_edge

    def origin(self) -> int:
        return fstOf3(self._hs_edge)

    def target(self) -> int:
        return sndOf3(self._hs_edge)

    def label(self) -> DGLinkLab:
        return thd(self._hs_edge)

    def name(self):
        return self.label().dglName()
