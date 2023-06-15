"""
Description :  Represents `Static.DevGraph.DGLinkLab`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Tuple, Optional

from .haskell import DGLinkLab, fstOf3, sndOf3, thd, gmorphismOfEdge, developmentGraphEdgeLabelName, \
    developmentGraphEdgeLabelId, getDevGraphLinkType, DevGraphLinkType, LinkKindGlobal, LinkKindLocal, LinkKindHiding, \
    LinkKindFree, LinkKindCofree, TheoremLink, showDoc
from .HsWrapper import HsHierarchyElement
from .GMorphism import GMorphism
from enum import Enum


class EdgeKind(Enum):
    UNKNOWN = -1
    GLOBAL = 0
    LOCAL = 1
    HIDING = 2
    FREE = 3
    COFREE = 4


class DevGraphEdge(HsHierarchyElement):
    def __init__(self, hs_edge: Tuple[int, int, DGLinkLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hs_edge = hs_edge

    def _type(self) -> DevGraphLinkType:
        return getDevGraphLinkType(self._label())

    def hs_obj(self):
        return self._hs_edge

    def origin(self) -> int:
        return fstOf3(self._hs_edge)

    def target(self) -> int:
        return sndOf3(self._hs_edge)

    def _label(self) -> DGLinkLab:
        return thd(self._hs_edge)

    def morphism(self) -> GMorphism:
        return GMorphism(gmorphismOfEdge(self._label()))

    def name(self) -> str:
        return developmentGraphEdgeLabelName(self._label())

    def id(self) -> int:
        return developmentGraphEdgeLabelId(self._label())

    def kind(self) -> EdgeKind:
        t = self._type()
        k = t.linkTypeKind()

        if isinstance(k, LinkKindGlobal):
            return EdgeKind.GLOBAL
        elif isinstance(k, LinkKindLocal):
            return EdgeKind.LOCAL
        elif isinstance(k, LinkKindHiding):
            return EdgeKind.HIDING
        elif isinstance(k, LinkKindFree):
            return EdgeKind.FREE
        elif isinstance(k, LinkKindCofree):
            return EdgeKind.COFREE
        else:
            return EdgeKind.UNKNOWN

    def is_homogeneous(self) -> bool:
        return self._type().linkTypeIsHomogenoeous()

    def info(self) -> str:
        return showDoc(self._label(), "")


class DefinitionDevGraphEdge(DevGraphEdge):
    pass


class TheoremDevGraphEdge(DevGraphEdge):
    def _type(self) -> TheoremLink:
        return super()._type()

    def is_proven(self):
        return self._type().linkTypeIsProven()

    def is_conservativ(self):
        return self._type().linkTypeIsConservativ()
