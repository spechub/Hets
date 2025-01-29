from typing import List

from hets import RefinementTreeLink, RefinementTreeNode

from .haskell import labNodes, labEdges


class RefinementTree:
    """
    Represents a refinement tree.

    Represents `Graph.Gr RTNodeLab RTLinkLab`.
    """
    _links: List[RefinementTreeLink]
    _nodes: List[RefinementTreeNode]

    def __init__(self, hs_refinement_tree):
        self._nodes = [RefinementTreeNode(n) for n in labNodes(hs_refinement_tree)]
        self._links = [RefinementTreeLink(e) for e in labEdges(hs_refinement_tree)]

    def nodes(self) -> List[RefinementTreeNode]:
        """
        Returns the nodes of the refinement tree.
        :return:
        """
        return self._nodes

    def edges(self) -> List[RefinementTreeLink]:
        """
        Returns the edges of the refinement tree.
        :return:
        """
        return self._links
