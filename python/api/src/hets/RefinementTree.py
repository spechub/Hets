import typing
from typing import List

from .haskell import RefinementTreeNode as HsRefinementTreeNode, RefinementTreeLink as HsRefinementTreeLink, Gr, \
    labNodes, labEdges, LNode, LEdge, fst, snd, sndOf3, thd, fstOf3, isRootNode, rtNodeLab, rtn_name



class RefinementTreeNode:
    def __init__(self, hs_node: typing.Tuple[int, HsRefinementTreeNode]):
        self._hs_node = hs_node

    def _label(self) -> HsRefinementTreeNode:
        return snd(self._hs_node)

    def is_root(self) -> bool:
        return isRootNode(self._label())

    def name(self) -> str:
        return rtn_name(rtNodeLab(self._label()))

    def id(self) -> int:
        return fst(self._hs_node)


class RefinementTreeLink:
    def __init__(self, hs_edge: typing.Tuple[int, int, HsRefinementTreeLink]):
        self._hs_edge = hs_edge

    def _label(self) -> HsRefinementTreeLink:
        return thd(self._hs_edge)

    def id(self) -> typing.Tuple[int, int]:
        return self.source_id(), self.target_id()

    def source_id(self) -> int:
        return fstOf3(self._hs_edge)

    def target_id(self) -> int:
        return sndOf3(self._hs_edge)


class RefinementTree:
    _links: List[RefinementTreeLink]
    _nodes: List[RefinementTreeNode]

    def __init__(self, hs_refinement_tree):
        self._nodes = [RefinementTreeNode(n) for n in labNodes(hs_refinement_tree)]
        self._links = [RefinementTreeLink(e) for e in labEdges(hs_refinement_tree)]

    def nodes(self) -> List[RefinementTreeNode]:
        return self._nodes

    def edges(self) -> List[RefinementTreeLink]:
        return self._links
