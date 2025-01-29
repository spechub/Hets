import typing

from hets.haskell import RefinementTreeNode as HsRefinementTreeNode, snd, isRootNode, rtn_name, rtNodeLab, fst


class RefinementTreeNode:
    """
    Represents a refinement tree node with their ID and label data.

    Represents `(Int, RTNodeLab)`.
    """
    def __init__(self, hs_node: typing.Tuple[int, HsRefinementTreeNode]):
        self._hs_node = hs_node

    def _label(self) -> HsRefinementTreeNode:
        return snd(self._hs_node)

    def is_root(self) -> bool:
        """
        Returns whether the node is a root node.
        :return: True if the node is a root node, False otherwise
        """
        return isRootNode(self._label())

    def name(self) -> str:
        """
        Returns the name of the node.
        :return:
        """
        return rtn_name(rtNodeLab(self._label()))

    def id(self) -> int:
        """
        Returns the ID of the node.
        :return:
        """
        return fst(self._hs_node)
