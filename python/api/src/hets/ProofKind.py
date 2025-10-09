from enum import Enum


class ProofKind(Enum):
    """
    Enum for the different kinds of proof results.
    """
    UNKNOWN = -1
    """ The proof result is unknown. """
    OPEN = 1
    """ The proof is still open. """
    PROVEN = 2
    """ The goal has been proven successfully. """
    PROVEN_BY_INCONSISTENCY = 3
    """ The goal has been proven by inconsistency. """
    DISPROVEN = 4
    """ The goal has been disproven. """
    TIMED_OUT = 5
    """ The proof timed out. """
    GUESSED = 6
    """ The proof result is guessed. """
    CONJECTURED = 7
    """ The goal is assumed to hold as a conjecture. """
    HANDWRITTEN = 8
    """ The goal is proven by a handwritten proof. """

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
