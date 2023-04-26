"""
Description :  Represents `Static.DgUtils.ConsStatus`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from .haskell import ConsStatus, showConsistencyStatus


class ConsistencyStatus:
    def __init__(self, hs_cons_status: ConsStatus):
        self._hs_cons_status = hs_cons_status

    def required(self) -> str:
        hsCons = self._hs_cons_status.requiredConservativity()
        return showConsistencyStatus(hsCons)

    def proven(self) -> str:
        hsCons = self._hs_cons_status.provenConservativity()
        return showConsistencyStatus(hsCons)

    def is_proven_link(self) -> bool:
        return self._hs_cons_status.isProvenConsStatusLink()
