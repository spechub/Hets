from .haskell import ConsStatus, showConsistencyStatus


class ConsistencyStatus:
    def __init__(self, hsConsStatus: ConsStatus):
        self._hsConsStatus = hsConsStatus

    def consistency(self) -> str:
        hsCons = self._hsConsStatus.getConsOfStatus()
        return showConsistencyStatus(hsCons)

    def isProvenLink(self) -> bool:
        return self._hsConsStatus.isProvenConsStatusLink()