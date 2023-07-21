from enum import Enum


class ProofKind(Enum):
    UNKNOWN = -1
    OPEN = 1
    PROVEN = 2
    PROVEN_BY_INCONSISTENCY = 3
    DISPROVEN = 4
    TIMED_OUT = 5
    GUESSED = 6
    CONJECTURED = 7
    HANDWRITTEN = 8

    def to_str(self) -> str:
        return {
            ProofKind.UNKNOWN: "Unknown",
            ProofKind.OPEN: "Open",
            ProofKind.PROVEN: "Proven",
            ProofKind.PROVEN_BY_INCONSISTENCY: "Proven by inconsistency",
            ProofKind.DISPROVEN: "Disproven",
            ProofKind.TIMED_OUT: "Timed out",
            ProofKind.GUESSED: "Guessed",
            ProofKind.CONJECTURED: "Conjectured",
            ProofKind.HANDWRITTEN: "Handwritten"
        }[self]
