import enum
import typing

from hets.haskell import RefinementTreeLink as HsRefinementTreeLink, thd, fstOf3, sndOf3, rtl_type, RTRefine, RTComp


class RefinementTreeLinkKind(enum.Enum):
    UNKNOWN = -1
    COMPONENT = 1
    SIMPLE = 2


class RefinementTreeLink:
    """
    Represents a link in a refinement tree with source and target node IDs and label data for the edge.

    Represents `(Int, Int, RTLinkLab)`.
    """

    def __init__(self, hs_edge: typing.Tuple[int, int, HsRefinementTreeLink]):
        self._hs_edge = hs_edge

    def _label(self) -> HsRefinementTreeLink:
        return thd(self._hs_edge)

    def id(self) -> typing.Tuple[int, int]:
        """
        Returns a tuple identifying the edge.
        :return:
        """
        return self.source_id(), self.target_id()

    def source_id(self) -> int:
        """
        Returns the ID of the source node.
        :return:
        """

        return fstOf3(self._hs_edge)

    def target_id(self) -> int:
        """
        Returns the ID of the target node.
        :return:
        """
        return sndOf3(self._hs_edge)

    def kind(self) -> RefinementTreeLinkKind:
        """
        Returns the kind of the link.
        :return:
        """
        typ = rtl_type(self._label())
        if isinstance(typ, RTRefine):
            return RefinementTreeLinkKind.SIMPLE
        elif isinstance(typ, RTComp):
            return RefinementTreeLinkKind.COMPONENT
        else:
            return RefinementTreeLinkKind.UNKNOWN
