"""
Description :  Represents `Static.DgUtils.ConsStatus`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from .ConsistencyKind import ConsistencyKind
from .haskell import ConsStatus, Conservativity, Inconsistent, Unknown, PCons, Cons, Mono, Def


class ConsistencyStatus:
    def __init__(self, hs_cons_status: ConsStatus):
        """
        Consistency status of a node.

        The status contains the required consistency as well as the result of a proven consistency (or :py:const:`~hets.ConsistencyKind.UNKNOWN` by default)

        :warning: This class should not be instantiated manually.

        :param hs_cons_status: Haskell object of ``HetsAPI.Internal.ConsStatus``
        """

        self._hs_cons_status = hs_cons_status

    def required(self) -> ConsistencyKind:
        hsCons = self._hs_cons_status.requiredConservativity()
        return self._hs_conservativity_to_consistency_kind(hsCons)

    def proven(self) -> ConsistencyKind:
        hsCons = self._hs_cons_status.provenConservativity()
        return self._hs_conservativity_to_consistency_kind(hsCons)

    def _hs_conservativity_to_consistency_kind(self, hs_cons: Conservativity):
        if isinstance(hs_cons, Inconsistent):
            return ConsistencyKind.INCONSISTENT
        elif isinstance(hs_cons, Unknown):
            return ConsistencyKind.UNKNOWN
        elif isinstance(hs_cons, PCons):
            return ConsistencyKind.PCONS
        elif isinstance(hs_cons, Cons):
            return ConsistencyKind.CONS
        elif isinstance(hs_cons, Mono):
            return ConsistencyKind.MONO
        elif isinstance(hs_cons, Def):
            return ConsistencyKind.DEFINED
        else:
            return ConsistencyKind.UNKNOWN

    def is_proven_link(self) -> bool:
        return self._hs_cons_status.isProvenConsStatusLink()
