"""
Description :  Represents `Static.DevGraph.DGLinkLab`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
import typing
from typing import Tuple, Optional, List

from .Theory import Theory
from .ConsistencyStatus import ConsistencyStatus
from .ConsistencyKind import ConsistencyKind
from .haskell import DGLinkLab, fstOf3, sndOf3, thd, gmorphismOfEdge, developmentGraphEdgeLabelName, \
    developmentGraphEdgeLabelId, getDevGraphLinkType, DevGraphLinkType, LinkKindGlobal, LinkKindLocal, LinkKindHiding, \
    LinkKindFree, LinkKindCofree, TheoremLink, showDoc, getUsableConservativityCheckers, \
    checkConservativityEdgeAndRecord, fst, snd, getEdgeConsStatus, diags, show, linkTypeKind, PyTheory, Conservativity, \
    LibEnv
from .ConservativityChecker import ConservativityChecker
from .Sentence import Sentence
from .HsWrapper import HsHierarchyElement
from .GMorphism import GMorphism
from .result import result_or_raise, result_to_optional
from .conversions import hs_conservativity_to_consistency_kind
from enum import Enum


class EdgeKind(Enum):
    """
    Enumeration of edge kinds.

    Abstraction over `Static.DevGraph.DGLinkLab`
    """

    # TODO: Add comments describing the different edge kinds

    UNKNOWN = -1
    """ Unknown edge kind """
    GLOBAL = 0
    LOCAL = 1
    HIDING = 2
    FREE = 3
    COFREE = 4


class DevGraphEdge(HsHierarchyElement):
    """
    Represents a development graph edge.

    Represents `Static.DevGraph.DGLinkLab` via `HetsAPI.Internal.DGLinkLab`
    """

    def __init__(self, hs_edge: Tuple[int, int, DGLinkLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hs_edge = hs_edge

    def _type(self) -> DevGraphLinkType:
        return getDevGraphLinkType(self._label())

    def hs_obj(self):
        return self._hs_edge

    def _pointer(self):
        """
        Returns a tuple to identify the edge in the DevelopmentGraph.
        :return:
        """
        name, env = self.root().hs_obj()

        return name, env, self._hs_edge

    def origin(self) -> int:
        """
        Returns the id of the origin node of the edge.
        :return: Id of the origin node
        """
        return fstOf3(self._hs_edge)

    def target(self) -> int:
        """
        Returns the id of the target node of the edge.
        :return: Id of the target node
        """
        return sndOf3(self._hs_edge)

    def _label(self) -> DGLinkLab:
        """
        Helper function to extract the label from the Haskell tuple.
        :return:
        """
        return thd(self._hs_edge)

    def morphism(self) -> GMorphism:
        """
        Returns the morphism of the edge.
        :return:
        """
        return GMorphism(gmorphismOfEdge(self._label()))

    def name(self) -> str:
        """
        Returns the name of the edge.
        :return:
        """
        return developmentGraphEdgeLabelName(self._label())

    def title(self) -> str:
        """
        Calculates a title of the edge.
        :return:
        """
        return f"{self.id()} {self.name()}({self.origin()} --> {self.target()})"

    def id(self) -> int:
        """
        Returns the id of the edge.
        :return:
        """
        return developmentGraphEdgeLabelId(self._label())

    def kind(self) -> EdgeKind:
        """
        Calculates and returns the kind of the edge.
        :return: Kind of the edge
        """
        t = self._type()
        k = linkTypeKind(t)

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
        """
        Checks whether the edge is homogeneous.
        :return: True if the edge is homogeneous, False otherwise
        """
        return self._type().linkTypeIsHomogenoeous()

    def is_inclusion(self) -> bool:
        """
        Checks whether the edge is an inclusion.
        :return: True if the edge is an inclusion, False otherwise
        """
        return self._type().linkTypeIsInclusion()

    def info(self) -> str:
        """
        Calculates a textual representation of the edge.
        :return:
        """
        return showDoc(self._label(), "")

    def get_usable_conservativity_checkers(self) -> typing.List[ConservativityChecker]:
        """
        Returns a list of usable conservativity checkers for this edge.
        :return: List of conservativity checkers
        """
        name, env = self.root().hs_obj()
        ccs = getUsableConservativityCheckers(self._hs_edge, env, name).act()

        return [ConservativityChecker(cc) for cc in ccs]

    def get_conservativity_checker_by_name(self, name: str) -> Optional[ConservativityChecker]:
        """
        Returns a (usable) conservativity checker by its name.
        :param name: Name of the conservativity checker
        :return: Conservativity checker if found, otherwise None
        """
        return next((cc for cc in self.get_usable_conservativity_checkers() if cc.name() == name), None)

    def conservativity(self) -> ConsistencyKind:
        """
        Returns the conservativity of the edge.

        Overridden in subclasses.
        :return:
        """
        return ConsistencyKind.UNKNOWN

    def conservativity_status(self) -> ConsistencyStatus:
        """
        Returns the consistency status of the edge.
        :return:
        """
        edge_lab = self._label()
        hs_cons_status = getEdgeConsStatus(edge_lab)
        return ConsistencyStatus(hs_cons_status)

    def check_conservativity(self, checker: ConservativityChecker) -> Tuple[Optional[ConsistencyKind], Optional[List[str]], Optional[List[str]], List[str]]:
        """
        Checks the conservativity of this edge

        :param checker: Checker to use for checking the conservativity
        :return: calculated conservativity together with obligations for the conservativity holding in the source theory and obligations required to hold in an imported theory
        """
        check_result = checkConservativityEdgeAndRecord(checker._hs_cons_checker, self._pointer()).act()

        result: Optional[Tuple[Tuple[Conservativity, PyTheory, PyTheory], LibEnv]] = result_to_optional(check_result)
        diagnosis = [show(d) for d in diags(check_result)]

        if result is None:
            return None, None, None, diagnosis

        conservativity_result = fst(result)
        new_env = snd(result)

        conservativity = fstOf3(conservativity_result)
        explanationsTheory = Theory(sndOf3(conservativity_result), None)
        obligationsTheory = Theory(thd(conservativity_result), None)

        explanations = [str(s) for s in explanationsTheory.sentences()]
        obligations = [str(s) for s in obligationsTheory.sentences()]

        self.root().hs_update(new_env)

        return hs_conservativity_to_consistency_kind(conservativity), explanations, obligations, diagnosis


class DefinitionDevGraphEdge(DevGraphEdge):
    """
    Represents a definitional edge in the development graph.
    """
    def conservativity(self) -> ConsistencyKind:
        return ConsistencyKind.DEFINITIONAL


class TheoremDevGraphEdge(DevGraphEdge):
    """
    Represents a theorem edge in the development graph.
    """

    def _type(self) -> TheoremLink:
        return super()._type()

    def is_proven(self) -> bool:
        """
        Returns whether the edge is proven.
        :return: True if the edge has been proven, False otherwise
        """
        return self._type().linkTypeIsProven()

    def is_conservativ(self) -> bool:
        """
        Returns whether the edge is conservativ.
        :return: True if the edge was checked to be conservativ, False otherwise
        """
        return self._type().linkTypeIsConservativ()

    def is_pending(self) -> bool:
        """
        Returns whether the edge has pending proofs.
        :return: True if the edge has pending proofs, False otherwise
        """
        return self._type().linkTypeIsPending()

    def conservativity(self) -> ConsistencyKind:
        if self.is_conservativ():
            return ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE

        return ConsistencyKind.UNKNOWN
