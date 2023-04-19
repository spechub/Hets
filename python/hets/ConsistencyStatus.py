"""
Description :  Represents `Static.DgUtils.ConsStatus`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from .haskell import ConsStatus, showConsistencyStatus


class ConsistencyStatus:
    def __init__(self, hsConsStatus: ConsStatus):
        self._hsConsStatus = hsConsStatus

    def required(self) -> str:
        hsCons = self._hsConsStatus.requiredConservativity()
        return showConsistencyStatus(hsCons)

    def proven(self) -> str:
        hsCons = self._hsConsStatus.provenConservativity()
        return showConsistencyStatus(hsCons)


    def isProvenLink(self) -> bool:
        return self._hsConsStatus.isProvenConsStatusLink()
