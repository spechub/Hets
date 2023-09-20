"""
Description :  Represents `Static.DevGraph.DGLinkLab`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
import typing
from typing import Tuple, Optional, List

from .ConsistencyStatus import ConsistencyStatus
from .ConsistencyKind import ConsistencyKind
from .haskell import DGLinkLab, fstOf3, sndOf3, thd, gmorphismOfEdge, developmentGraphEdgeLabelName, \
    developmentGraphEdgeLabelId, getDevGraphLinkType, DevGraphLinkType, LinkKindGlobal, LinkKindLocal, LinkKindHiding, \
    LinkKindFree, LinkKindCofree, TheoremLink, showDoc, getUsableConservativityCheckers, \
    checkConservativityEdgeAndRecord, fst, snd, getEdgeConsStatus, diags, show, linkTypeKind
from .ConservativityChecker import ConservativityChecker
from .Sentence import Sentence
from .HsWrapper import HsHierarchyElement
from .GMorphism import GMorphism
from .result import result_or_raise, result_to_optional
from .conversions import hs_conservativity_to_consistency_kind
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

    def _pointer(self):
        name, env = self.root().hs_obj()

        return name, env, self._hs_edge

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

    def title(self) -> str:
        return f"{self.id()} {self.name()}({self.origin()} --> {self.target()})"

    def id(self) -> int:
        return developmentGraphEdgeLabelId(self._label())

    def kind(self) -> EdgeKind:
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
        return self._type().linkTypeIsHomogenoeous()

    def is_inclusion(self) -> bool:
        return self._type().linkTypeIsInclusion()

    def info(self) -> str:
        return showDoc(self._label(), "")

    def get_usable_conservativity_checkers(self) -> typing.List[ConservativityChecker]:
        name, env = self.root().hs_obj()
        ccs = getUsableConservativityCheckers(self._hs_edge, env, name).act()

        return [ConservativityChecker(cc) for cc in ccs]

    def get_conservativity_checker_by_name(self, name: str) -> Optional[ConservativityChecker]:
        return next((cc for cc in self.get_usable_conservativity_checkers() if cc.name() == name), None)

    def conservativity(self) -> ConsistencyKind:
        return ConsistencyKind.UNKNOWN

    def conservativity_status(self) -> ConsistencyStatus:
        edge_lab = self._label()
        hs_cons_status = getEdgeConsStatus(edge_lab)
        return ConsistencyStatus(hs_cons_status)


class DefinitionDevGraphEdge(DevGraphEdge):
    def conservativity(self) -> ConsistencyKind:
        return ConsistencyKind.DEFINITIONAL


class TheoremDevGraphEdge(DevGraphEdge):
    def _type(self) -> TheoremLink:
        return super()._type()

    def is_proven(self) -> bool:
        return self._type().linkTypeIsProven()

    def is_conservativ(self) -> bool:
        return self._type().linkTypeIsConservativ()

    def is_pending(self) -> bool:
        return self._type().linkTypeIsPending()

    def check_conservativity(self, checker: ConservativityChecker) -> Tuple[Optional[ConsistencyKind], Optional[List[Sentence]], Optional[List[Sentence]], List[str]]:
        """
        Checks the conservativity of this edge

        :param checker: Checker to use for checking the conservativity
        :return: calculated conservativity together with obligations for the conservativity holding in the source theory and obligations required to hold in an imported theory
        """
        check_result = checkConservativityEdgeAndRecord(checker._hs_cons_checker, self._pointer()).act()

        result = result_to_optional(check_result)
        diagnosis = [show(d) for d in diags(check_result)]

        if result is None:
            return None, None, None, diagnosis

        conservativity_result = fst(result)
        new_env = snd(result)

        conservativity = fstOf3(conservativity_result)
        explanations_names = sndOf3(conservativity_result)
        obligations_names = thd(conservativity_result)

        graph = self.parent()
        target = graph.node_by_id(self.target())
        target_theory = target.global_theory()

        explanations = [target_theory.sentence_by_name(s) for s in explanations_names]
        obligations = [target_theory.sentence_by_name(s) for s in obligations_names]

        self.root().hs_update(new_env)

        return hs_conservativity_to_consistency_kind(conservativity), explanations, obligations, diagnosis

    def conservativity(self) -> ConsistencyKind:
        if self.is_conservativ():
            return ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE

        return ConsistencyKind.UNKNOWN
