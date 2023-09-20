from enum import Enum


class ConsistencyKind(Enum):
    """
    A type of consistency of a theory.
    """

    INCONSISTENT = 0
    """
    The theory was proven to be inconsistent
    """

    UNKNOWN = 1
    """
    The consistency of the theory is not known
    """

    PROOF_THEORETICALLY_CONSERVATIVE = 2
    """
    The theory is proof-theoretically conservative
    """

    CONSERVATIVE = 3
    """
    The theory is conservative
    """

    MONOMORPHIC = 4
    """
    The theory is monomorphic
    """

    DEFINITIONAL = 5
    """
    The theory is definitional
    """

    ERROR = 6
    """
    An error occurred
    """

    TIMED_OUT = 7
    """
    The consistency checker timed out
    """

    NONE = 8
    """
    There is no consistency
    """

    def to_str(self) -> str:
        """
        Converts a consistency kind to human friendly string
        """

        return {
            ConsistencyKind.INCONSISTENT: "Inconsistent",
            ConsistencyKind.UNKNOWN: "Unknown",
            ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE: "Proof-theoretically conservative",
            ConsistencyKind.CONSERVATIVE: "Conservative",
            ConsistencyKind.MONOMORPHIC: "Monomorphic",
            ConsistencyKind.DEFINITIONAL: "Definitional",
            ConsistencyKind.ERROR: "Errored",
            ConsistencyKind.TIMED_OUT: "Timed out",
            ConsistencyKind.NONE: "None"
        }[self]

    def short_name(self) -> str:
        """
        Returns an abbreviated form of the kinds name
        """

        return {
            ConsistencyKind.INCONSISTENT: "NotCons",
            ConsistencyKind.UNKNOWN: "Unknown",
            ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE: "PCons",
            ConsistencyKind.CONSERVATIVE: "Cons",
            ConsistencyKind.MONOMORPHIC: "Mono",
            ConsistencyKind.DEFINITIONAL: "Def",
            ConsistencyKind.ERROR: "Err",
            ConsistencyKind.TIMED_OUT: "TimeOut",
            ConsistencyKind.NONE: ""
        }[self]
