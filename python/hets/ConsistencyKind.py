from enum import Enum


class ConsistencyKind(Enum):
    INCONSISTENT = 0
    UNKNOWN = 1
    PCONS = 2
    CONS = 3
    MONO = 4
    DEFINED = 5
    ERROR = 6
    TIMED_OUT = 7

    def to_str(self) -> str:
        return {
            ConsistencyKind.INCONSISTENT: "Inconsistent",
            ConsistencyKind.UNKNOWN: "Unknown",
            ConsistencyKind.PCONS: "PCons",
            ConsistencyKind.CONS: "Consistent",
            ConsistencyKind.MONO: "Mono",
            ConsistencyKind.DEFINED: "Defined",
            ConsistencyKind.ERROR: "Errored",
            ConsistencyKind.TIMED_OUT: "Timed out"
        }[self]
