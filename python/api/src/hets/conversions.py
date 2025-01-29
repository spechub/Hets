from hets import ConsistencyKind
from hets.haskell import Conservativity, Inconsistent, Unknown, PCons, Cons, Mono, Def


def hs_conservativity_to_consistency_kind(hs_cons: Conservativity) -> ConsistencyKind:
    """
    Converts a Haskell conservativity to a Python ConsistencyKind.
    :param hs_cons: Haskell conservativity
    :return: Python ConsistencyKind
    """
    if isinstance(hs_cons, Inconsistent):
        return ConsistencyKind.INCONSISTENT
    elif isinstance(hs_cons, Unknown):
        return ConsistencyKind.UNKNOWN
    elif isinstance(hs_cons, PCons):
        return ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE
    elif isinstance(hs_cons, Cons):
        return ConsistencyKind.CONSERVATIVE
    elif isinstance(hs_cons, Mono):
        return ConsistencyKind.MONOMORPHIC
    elif isinstance(hs_cons, Def):
        return ConsistencyKind.DEFINITIONAL
    else:
        return ConsistencyKind.NONE
