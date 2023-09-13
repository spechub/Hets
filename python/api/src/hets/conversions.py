from hets import ConsistencyKind
from hets.haskell import Conservativity, Inconsistent, Unknown, PCons, Cons, Mono, Def


def hs_conservativity_to_consistency_kind(hs_cons: Conservativity) -> ConsistencyKind:
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
        return ConsistencyKind.DEFINITIONAL
    else:
        return ConsistencyKind.UNKNOWN
